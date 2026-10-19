module

public import Mathlib

@[expose] public section

/-!
# Entropy certificate for the triangle variational problem

This is the statement of Proposition 7.2 in version 1 of Matthew Kwan and
Huy Tuan Pham, "Nonlinear lower-tail large deviations at criticality"
(arXiv:2610.10233v1).

For every nonnegative parameter α, there is an attained global minimum M of
the balanced two-block objective on [0,1]² and a continuous function G on
[0,1] such that entropyF α G is at least M throughout [0,1]³. The logarithm
is Lean's real logarithm, with log 0 = 0, so H 0 = 1.

Only this analytic certificate lemma is claimed here. Its application to
triangle-free random graphs and the other results of the paper are outside
the formalized statement. Target supplies the proof independently of this
module's deliberate theorem hole.
-/

set_option autoImplicit false
namespace TriangleNumerical
noncomputable section

def unitInterval : Set ℝ := Set.Icc 0 1

def H (w : ℝ) : ℝ := 1 - w + w * Real.log w

/-- Balanced two-block objective: r within each part, t between parts. -/
def twoBlockObjective (α r t : ℝ) : ℝ :=
  (H r + H t) / 2 + α * (r ^ 3 + 3 * r * t ^ 2) / 4

/-- Attainment AND a lower bound, not an unspecified stationary branch. -/
def IsTwoBlockMinimum (α M : ℝ) : Prop :=
  (∃ r ∈ unitInterval, ∃ t ∈ unitInterval,
    twoBlockObjective α r t = M) ∧
  (∀ r ∈ unitInterval, ∀ t ∈ unitInterval,
    M ≤ twoBlockObjective α r t)

def entropyF (α : ℝ) (G : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (H a + H b + H c) / 3 + α * a * b * c
    - (G a * G b + G a * G c + G b * G c)

def EntropyCertificateProposition : Prop :=
  ∀ α : ℝ, 0 ≤ α →
    ∃ (M : ℝ) (G : ℝ → ℝ),
      IsTwoBlockMinimum α M ∧
      ContinuousOn G unitInterval ∧
      ∀ a ∈ unitInterval, ∀ b ∈ unitInterval, ∀ c ∈ unitInterval,
        M ≤ entropyF α G a b c

/-- The reference statement. Comparator checks the candidate proof separately. -/
theorem entropy_certificate : EntropyCertificateProposition := by
  sorry

end
end TriangleNumerical
