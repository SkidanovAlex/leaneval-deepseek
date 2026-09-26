import Submission.Helpers
import Submission.PropertyT
import Mathlib

open OnPropertyT
open scoped BigOperators

set_option autoImplicit false

namespace Submission.RouteB

noncomputable section

variable {G : Type*} [Group G]

/-!
# The algebraic property-(T) certificate: first fundamentals (Route B)

The challenge statement uses Ozawa's algebraic form of Kazhdan's property (T):
`PropertyT G` asks for a finite symmetric generating set `S` with
`closure S = ⊤` and elements `Λ > 0`, `ξ : Finset ℝG` with

    Δ_S ^ 2 - Λ • Δ_S = ∑_{x ∈ ξ} star x * x.

This file collects the first, purely algebraic, pieces of the road towards the
paper's certificate (Kaluba–Kielak–Nowak, *On property (T) for Aut(F_n) and
SL_n(Z)*, Annals 193 (2021)):

* `two_mul_laplacian_eq_sum_sq` — the paper's equation (1),
  `2·Δ = ∑_{s∈S} (1-s)*(1-s)` for symmetric `S` (so `Δ` is *twice* a sum of
  hermitian squares, the form in which it is an order unit of the augmentation
  ideal);
* `propertyT_finite` — **every finite group satisfies the certificate** with
  `S = G`, `Λ = |G|` and the empty square sum: the sum of all group elements is
  `|G|`-times idempotent.  This is the basic sanity check of the definition and
  a base case for transfer arguments;
* `sum_sq_via_gram` — the SDP-to-SOS bridge: a Gram factorization `P = Q Qᵀ`
  yields a decomposition `∑_j star ξ_j * ξ_j` with `ξ_j = ∑_i Q i j • x_i` on a
  chosen basis `x`; this is the step that turns a numerical solution of the
  semidefinite programme into an algebraic certificate (the missing input for
  the paper's groups is the actual matrix `Q`, deposited - numerically only -
  in the Zenodo record of the paper).
-/

/-! ## The SDP-to-SOS bridge -/

/-- **Gram factorization gives a sum of hermitian squares.**  For a finite
family `x : ι → ℝG` and a real matrix `Q : ι → κ → ℝ`, the squares of the
elements `ξ_j = ∑_i Q i j • x_i` expand as the Gram combination with
`P i i' = ∑_j Q i j * Q i' j`:
`∑_j star ξ_j * ξ_j = ∑_{i,i'} P i i' • (star (x i) * x i')`.
In particular, if `Δ² - λΔ = ∑_{i,i'} P i i' • (star (x i) * x i')` is the
`(OP)` formulation of the paper for the basis `x`, then `P = Q Qᵀ` (a positive
semidefinite certificate for the semidefinite programme) yields the algebraic
certificate. -/
theorem sum_sq_via_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → MonoidAlgebra ℝ G) (Q : ι → κ → ℝ) :
    (∑ j : κ, star (∑ i : ι, Q i j • x i) * (∑ i : ι, Q i j • x i)) =
      ∑ i : ι, ∑ i' : ι, (∑ j : κ, Q i j * Q i' j) • (star (x i) * x i') := by
  classical
  have hstar : ∀ j : κ, star (∑ i : ι, Q i j • x i) = ∑ i : ι, Q i j • star (x i) := by
    intro j
    rw [Submission.Helpers.star_sum]
    exact Finset.sum_congr rfl (fun i _ => Submission.Helpers.star_smul (Q i j) (x i))
  rw [Finset.sum_congr rfl (fun j _ => by rw [hstar j])]
  have hstep : ∀ j : κ,
      (∑ i : ι, Q i j • star (x i)) * (∑ i : ι, Q i j • x i) =
        ∑ i : ι, ∑ i' : ι, (Q i j * Q i' j) • (star (x i) * x i') := by
    intro j
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => by
      rw [smul_mul_smul]))
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i' _ => (Finset.sum_smul).symm)

/-! ## The finite-group base case -/

/-- A natural-number scalar multiple in a group ring is the corresponding
natural-number coefficient times the element. -/
lemma smul_natCast_eq_natCast_mul (c : ℕ) (Z : MonoidAlgebra ℝ G) :
    ((c : ℝ) • Z) = ((c : ℕ) : MonoidAlgebra ℝ G) * Z := by
  rw [Algebra.smul_def, map_natCast]

/-- The sum of all group elements of a finite group is `|G|`-times idempotent:
`(∑_g g) * (∑_g g) = |G| · ∑_g g`. -/
theorem sum_univ_mul_self [Fintype G] :
    (∑ g : G, MonoidAlgebra.of ℝ G g) * (∑ g : G, MonoidAlgebra.of ℝ G g) =
      ((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) *
        (∑ g : G, MonoidAlgebra.of ℝ G g) := by
  classical
  have hmul : ∀ u : G, (∑ g : G, MonoidAlgebra.of ℝ G g) * MonoidAlgebra.of ℝ G u =
      ∑ g : G, MonoidAlgebra.of ℝ G g := by
    intro u
    rw [Finset.sum_mul]
    rw [show (∑ g : G, MonoidAlgebra.of ℝ G g * MonoidAlgebra.of ℝ G u) =
        ∑ g : G, MonoidAlgebra.of ℝ G (g * u) by
      exact Finset.sum_congr rfl (fun g _ => (map_mul (MonoidAlgebra.of ℝ G) g u).symm)]
    exact Fintype.sum_equiv (Equiv.mulRight u) (fun g : G => MonoidAlgebra.of ℝ G (g * u))
      (fun g : G => MonoidAlgebra.of ℝ G g) (fun g => rfl)
  rw [Finset.mul_sum]
  rw [show (∑ u : G, (∑ g : G, MonoidAlgebra.of ℝ G g) * MonoidAlgebra.of ℝ G u) =
      ∑ _u : G, (∑ g : G, MonoidAlgebra.of ℝ G g) by
    exact Finset.sum_congr rfl (fun u _ => hmul u)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **A finite group satisfies the certificate with `S = G` and `Λ = |G|`.**
The Laplacian of the full group is `|G|`-times idempotent, so
`Δ² - |G|·Δ = 0` is a (trivial) sum of hermitian squares. -/
theorem laplacian_univ_sq [Fintype G] :
    OnPropertyT.Laplacian (Finset.univ : Finset G) ^ 2 =
      (Fintype.card G : ℝ) • OnPropertyT.Laplacian (Finset.univ : Finset G) := by
  classical
  have hcard : Nat.card ↥(Finset.univ : Finset G) = Fintype.card G := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_univ]
  have hA := sum_univ_mul_self (G := G)
  have hL : OnPropertyT.Laplacian (Finset.univ : Finset G)
      = ((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) - ∑ g : G, MonoidAlgebra.of ℝ G g := by
    unfold OnPropertyT.Laplacian
    rw [hcard]
  have hmain : (((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) - ∑ g : G, MonoidAlgebra.of ℝ G g)
        * (((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) - ∑ g : G, MonoidAlgebra.of ℝ G g)
      = ((Fintype.card G : ℕ) : MonoidAlgebra ℝ G)
        * (((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) - ∑ g : G, MonoidAlgebra.of ℝ G g) := by
    have hcA : (∑ g : G, MonoidAlgebra.of ℝ G g) * ((Fintype.card G : ℕ) : MonoidAlgebra ℝ G)
        = ((Fintype.card G : ℕ) : MonoidAlgebra ℝ G) * (∑ g : G, MonoidAlgebra.of ℝ G g) :=
      (Nat.cast_comm (Fintype.card G) (∑ g : G, MonoidAlgebra.of ℝ G g)).symm
    rw [sub_mul, mul_sub, mul_sub, hA, hcA]
    noncomm_ring
  rw [hL, smul_natCast_eq_natCast_mul, sq, hmain]

/-- **Every finite group has property (T)** in the algebraic (Ozawa)
certificate form of `ChallengeDeps.PropertyT`. -/
theorem propertyT_finite (G : Type*) [Group G] [Fintype G] : PropertyT G := by
  classical
  refine ⟨Finset.univ, ?_, ?_, (Fintype.card G : ℝ), ?_, ∅, ?_⟩
  · ext g
    simp
  · rw [Finset.coe_univ]; exact Subgroup.closure_univ
  · exact_mod_cast (Fintype.card_pos_iff.mpr ⟨1⟩)
  · rw [Finset.sum_empty, laplacian_univ_sq, sub_self]

/-! ## The paper's form of the Laplacian -/

/-- **The paper's equation (1).**  For a symmetric generating set `S`, twice the
Twice the Laplacian is the sum of hermitian squares of the augmentation-ideal elements
`1 - s`: `2·Δ_S = ∑_{s∈S} star (1-s) * (1-s)`. -/
theorem two_mul_laplacian_eq_sum_sq (S : Finset G) (hsym : (S : Set G)⁻¹ = S) :
    (2 : MonoidAlgebra ℝ G) * OnPropertyT.Laplacian S =
      ∑ s ∈ S, star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s) := by
  classical
  have hterm : ∀ s : G,
      star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s) =
        (2 : MonoidAlgebra ℝ G) - MonoidAlgebra.of ℝ G s - MonoidAlgebra.of ℝ G s⁻¹ := by
    intro s
    have hss : MonoidAlgebra.of ℝ G s⁻¹ * MonoidAlgebra.of ℝ G s = 1 := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
      simp [MonoidAlgebra.one_def]
    rw [Submission.Helpers.star_sub, Submission.Helpers.star_one, Submission.Helpers.star_of,
      sub_mul, one_mul, mul_sub, mul_one, hss]
    rw [show (2 : MonoidAlgebra ℝ G) = 1 + 1 by norm_num]
    abel
  have hsum_inv : (∑ s ∈ S, MonoidAlgebra.of ℝ G s⁻¹) = ∑ s ∈ S, MonoidAlgebra.of ℝ G s := by
    refine Finset.sum_bij (fun s _ => s⁻¹) (fun s hs => ?_) (fun a _ b _ hab => inv_injective hab)
      (fun b hb => ⟨b⁻¹, ?_, by simp⟩) (fun a _ => rfl)
    · exact Submission.PropertyT.inv_mem_of_mem hsym hs
    · exact Submission.PropertyT.inv_mem_of_mem hsym hb
  have hcard : (Nat.card ↥S : MonoidAlgebra ℝ G) = ((S.card : ℕ) : MonoidAlgebra ℝ G) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, hsum_inv]
  unfold OnPropertyT.Laplacian
  rw [hcard, nsmul_eq_mul]
  noncomm_ring

end

end Submission.RouteB
