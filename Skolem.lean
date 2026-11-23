import Init

/-!
# The Skolem problem over the rationals

Eric W. Weisstein, ["Skolem Problem"](https://mathworld.wolfram.com/SkolemProblem.html), MathWorld.
-/

set_option autoImplicit false

namespace Skolem

/-- Finite input for a homogeneous linear recurrence over the rationals. -/
structure Instance where
  order : Nat
  order_pos : 0 < order
  /-- Index `i` stores the source's coefficient `a_(i+1)`. -/
  coeff : Fin order → Rat
  /-- Index `i` stores the initial term `u_i`. -/
  initial : Fin order → Rat
  last_coeff_ne_zero : coeff ⟨order - 1, by omega⟩ ≠ 0

namespace Instance

/-- `window` lists the preceding terms from oldest to newest. -/
def recurrenceRhs (x : Instance) (window : Fin x.order → Rat) : Rat :=
  (List.ofFn fun i => x.coeff i * window i.rev).sum

/-- The initial conditions and recurrence equation at every natural index. -/
def IsSequence (x : Instance) (u : Nat → Rat) : Prop :=
  (∀ i : Fin x.order, u i.val = x.initial i) ∧
  (∀ n : Nat, u (n + x.order) = x.recurrenceRhs fun i => u (n + i.val))

/-- The term determined by the finite input. -/
def term (x : Instance) (n : Nat) : Rat :=
  if h : n < x.order then
    x.initial ⟨n, h⟩
  else
    x.recurrenceRhs fun i => term x (n - x.order + i.val)
termination_by n
decreasing_by
  have hi := i.isLt
  omega

theorem term_isSequence (x : Instance) : x.IsSequence x.term := by
  constructor
  · intro i
    rw [term, dite_eq_left i.isLt]
  · intro n
    have h : ¬ n + x.order < x.order := by omega
    rw [term, dite_eq_right h, Nat.add_sub_cancel]

theorem sequence_unique (x : Instance) (u : Nat → Rat) (hu : x.IsSequence u) :
    u = x.term := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < x.order
    · exact (hu.1 ⟨n, h⟩).trans (x.term_isSequence.1 ⟨n, h⟩).symm
    · have hn : n - x.order + x.order = n := by omega
      calc
        u n = x.recurrenceRhs (fun i => u (n - x.order + i.val)) := by
          simpa only [hn] using hu.2 (n - x.order)
        _ = x.recurrenceRhs (fun i => x.term (n - x.order + i.val)) := by
          congr 1
          funext i
          apply ih
          have hi := i.isLt
          omega
        _ = x.term n := by
          simpa only [hn] using (x.term_isSequence.2 (n - x.order)).symm

/-- The yes-instances of the Skolem problem. The index may be zero. -/
def HasZero (x : Instance) : Prop :=
  ∃ n : Nat, x.term n = 0

theorem hasZero_iff (x : Instance) (u : Nat → Rat) (hu : x.IsSequence u) :
    x.HasZero ↔ ∃ n : Nat, u n = 0 := by
  simp only [HasZero, x.sequence_unique u hu]

end Instance

/-- Correctness specification for a candidate Boolean decision procedure. -/
def Solves (answer : Instance → Bool) : Prop :=
  ∀ x : Instance, answer x = true ↔ x.HasZero

end Skolem
