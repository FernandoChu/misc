import Mathlib

------------------
-- Non-indexed W-types
------------------

-- The data of a signature `B -> A`
variable (A : Type) (B : A → Type)

inductive W (A : Type) (B : A → Type) : Type where
  | sup (a : A) (s : B a → W A B) : W A B

abbrev WNat : Type := W Bool (fun b => if b then Empty else Unit)

namespace WNat

def z : WNat := .sup true (fun x => x.elim)

def s : WNat → WNat :=
  fun w => .sup false (fun _ ↦ w)

def toNat : WNat → Nat
  | .sup true _ => 0
  | .sup false s => .succ (toNat (s ()))

def fromNat : Nat → WNat
  | 0 => z
  | n + 1 => s (fromNat n)

theorem eta (n : WNat) : fromNat (toNat n) = n := by
  induction n with
  | sup a s ih =>
    cases a
    · simp only [toNat, fromNat, WNat.s]
      congr 1
      funext u
      cases u
      exact ih ()
    · simp only [toNat, fromNat, z, ↓dreduceIte, W.sup.injEq, heq_eq_eq, true_and]
      funext a
      aesop

theorem epsilon (n : Nat) : toNat (fromNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fromNat, s, toNat, ih]

end WNat

-- `List X` as a W-type.
-- Constructors are labels `Option X`:
--   `none`   — `nil`,  no recursive arguments
--   `some x` — `cons x`, one recursive argument
abbrev WList (X : Type) : Type :=
  W (Option X) (fun a => match a with | none => Empty | some _ => Unit)

namespace WList

variable {X : Type}

def nil : WList X := .sup none Empty.elim

def cons (x : X) (xs : WList X) : WList X := .sup (some x) (fun _ => xs)

def toList : WList X → List X
  | .sup none _ => []
  | .sup (some x) s => x :: toList (s ())

def fromList : List X → WList X
  | [] => nil
  | x :: xs => cons x (fromList xs)

theorem eta (w : WList X) : fromList (toList w) = w := by
  induction w with
  | sup a s ih =>
    cases a
    · simp only [toList, fromList, nil]
      congr 1
      funext x
      exact x.elim
    · simp only [toList, fromList, cons]
      congr 1
      funext u
      cases u
      exact ih ()

theorem epsilon (l : List X) : toList (fromList l) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [toList, fromList, cons, ih]

end WList

------------------
-- Indexed W-types
------------------

-- The data of a signature `I <- B -> A -> I`
variable {I : Type} (A : I → Type) (B : (j : I) → A j → I → Type)

inductive IW {I : Type} (A : I → Type) (B : (j : I) → A j → I → Type) :
    I → Type where
  | sup (j : I) (a : A j) (s : (i : I) → (b : B j a i) → IW A B i) : IW A B j

-- `Fin` as an indexed W-type.
-- At index `n+1` there are two constructors:
--   `true`  — `zero`, with no recursive arguments
--   `false` — `succ`, with one recursive argument at index `n`
-- At index `0` there are no constructors (`Empty`).
abbrev FinA : Nat → Type
  | 0 => Empty
  | _ + 1 => Bool

abbrev FinB : (j : Nat) → FinA j → Nat → Type
  | 0, a, _ => a.elim
  | _ + 1, true, _ => Empty
  | n + 1, false, i => PLift (n = i)

abbrev WFin : Nat → Type := IW FinA FinB

namespace WFin

def zero (n : Nat) : WFin (n+1) :=
  .sup (n+1) true (fun _ b => b.elim)

def succ {n : Nat} (w : WFin n) : WFin (n+1) :=
  .sup (n+1) false (fun _ h => h.down ▸ w)

def toFin : (n : Nat) → WFin n → Fin n
  | 0, .sup _ a _ => a.elim
  | _ + 1, .sup _ true _ => ⟨0, Nat.succ_pos _⟩
  | n + 1, .sup _ false s =>
    let k := toFin n (s n (PLift.up rfl))
    ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

def ofFin : (n : Nat) → Fin n → WFin n
  | 0, k => k.elim0
  | _ + 1, ⟨0, _⟩ => zero _
  | n + 1, ⟨k + 1, h⟩ => succ (ofFin n ⟨k, Nat.lt_of_succ_lt_succ h⟩)

theorem epsilon : (n : Nat) → (k : Fin n) → toFin n (ofFin n k) = k
  | 0, k => k.elim0
  | _ + 1, ⟨0, _⟩ => rfl
  | n + 1, ⟨k + 1, h⟩ => by
    have ih := epsilon n ⟨k, Nat.lt_of_succ_lt_succ h⟩
    simp [ofFin, succ, toFin, ih]

theorem eta (n : Nat) (w : WFin n) : ofFin n (toFin n w) = w := by
  induction w with
  | sup j a s ih =>
    match j, a, s, ih with
    | 0, a, _, _ => exact a.elim
    | _ + 1, true, _, _ =>
      simp only [toFin, ofFin, zero]
      congr 1
      funext i b
      exact b.elim
    | _ + 1, false, s, ih =>
      simp only [toFin, ofFin, succ]
      congr 1
      funext i h
      obtain ⟨heq⟩ := h
      subst heq
      exact ih _ (PLift.up rfl)

end WFin

------------------
-- Identity type as an indexed W-type
------------------

-- The index set is `α × α`. At each index `(x, y)` there is one constructor
-- per proof of `x = y`, with no recursive arguments. So `WId α x y` is
-- inhabited exactly when `x = y`.
abbrev WId (α : Type) (x y : α) : Type :=
  IW (I := α × α)
    (fun p => PLift (p.1 = p.2))
    (fun _ _ _ => Empty)
    (x, y)

namespace WId

def refl {α : Type} (a : α) : WId α a a :=
  .sup (a, a) (PLift.up rfl) (fun _ b => b.elim)

def toEq {α : Type} {x y : α} : WId α x y → x = y
  | .sup _ ⟨h⟩ _ => h

def ofEq {α : Type} {x y : α} : x = y → WId α x y
  | rfl => refl x

theorem epsilon {α : Type} {x y : α} (h : x = y) : toEq (ofEq h) = h := by
  cases h; rfl

theorem eta {α : Type} {x y : α} (w : WId α x y) : ofEq (toEq w) = w := by
  rcases w with ⟨_, ⟨h⟩, s⟩
  simp only at h
  subst h
  simp only [ofEq, refl]
  congr 1
  funext _ b
  exact b.elim

end WId

-- `Vector X n` as an indexed W-type.
-- At index `0` the only constructor is `nil`, carrying no data and no recursive
-- arguments. At index `n+1` there is one constructor per `x : X` (`cons x`),
-- carrying one recursive argument at index `n`.
abbrev VecA (X : Type) : Nat → Type
  | 0 => Unit
  | _ + 1 => X

abbrev VecB (X : Type) : (j : Nat) → VecA X j → Nat → Type
  | 0, _, _ => Empty
  | n + 1, _, i => PLift (n = i)

abbrev WVec (X : Type) : Nat → Type := IW (VecA X) (VecB X)

namespace WVec

variable {X : Type}

def nil : WVec X 0 :=
  .sup 0 () (fun _ b => b.elim)

def cons {n : Nat} (x : X) (xs : WVec X n) : WVec X (n+1) :=
  .sup (n+1) x (fun _ h => h.down ▸ xs)

def toVec : (n : Nat) → WVec X n → List.Vector X n
  | 0, _ => ⟨[], rfl⟩
  | n + 1, .sup _ x s =>
    let v := toVec n (s n (PLift.up rfl))
    ⟨x :: v.1, by simp [v.2]⟩

def ofVec : (n : Nat) → List.Vector X n → WVec X n
  | 0, _ => nil
  | n + 1, ⟨[], h⟩ => by simp at h
  | n + 1, ⟨x :: xs, h⟩ => cons x (ofVec n ⟨xs, by simpa using h⟩)

theorem epsilon : (n : Nat) → (v : List.Vector X n) → toVec n (ofVec n v) = v
  | 0, ⟨[], _⟩ => rfl
  | 0, ⟨_ :: _, h⟩ => by simp at h
  | n + 1, ⟨[], h⟩ => by simp at h
  | n + 1, ⟨x :: xs, h⟩ => by
    have ih := epsilon n ⟨xs, by simpa using h⟩
    simp [ofVec, toVec, cons, ih]

theorem eta (n : Nat) (w : WVec X n) : ofVec n (toVec n w) = w := by
  induction w with
  | sup j a s ih =>
    match j, a, s, ih with
    | 0, _, _, _ =>
      simp only [ofVec, nil]
      congr 1
      funext i b
      exact b.elim
    | n + 1, _, s, ih =>
      simp only [toVec, ofVec, cons]
      congr 1
      funext i h
      obtain ⟨heq⟩ := h
      subst heq
      exact ih _ (PLift.up rfl)

end WVec
