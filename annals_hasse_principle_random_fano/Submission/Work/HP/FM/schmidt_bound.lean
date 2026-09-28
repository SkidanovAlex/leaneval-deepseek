import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.gon
import Submission.Work.HP.ball_count_small
import Submission.Work.HP.FM.primBasisGen
import Submission.Work.HP.FM.latStep_min
import Submission.Work.HP.FM.latStep_count

/-!
# Schmidt's bound for lattice points in a ball

`Work.HP.FM.schmidt_bound`: there is a constant `K = K(ι) > 0` such that for every sublattice
`L ⊆ ℤ^ι` and every `T ≥ 1`

`#(L ∩ B(T)) ≤ K · ∏_{i=1}^{rk L} (T / λ_i(L) + 1)`,

where `λ_i(L)` are the successive minima of `L` for the Euclidean unit ball.

The proof is an induction on the rank: the presentation of `L` is written in coefficient space
as an injective `ℝ`-linear map `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι`; one peels off a
shortest lattice vector `u` (obtained from `lat_min_attained`), projects orthogonally onto `u^⊥`
(`latStep`), and recurses.  The three ingredients of one step are
the injectivity of the peeled presentation (`recStep_injective`), `latStep_count` (fibre
counting) and `latStep_min` (the successive minima of the projected lattice dominate
`λ_2, λ_3, …` up to a factor `2`).
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant of the induction: `K_0 = 1`, `K_{n+1} = 2^{n+1} K_n`. -/
def Kc : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 2 ^ (n + 1) * Kc n

lemma Kc_succ (n : ℕ) : Kc (n + 1) = 2 ^ (n + 1) * Kc n := rfl

lemma Kc_nonneg : ∀ n, 0 ≤ Kc n := by
  intro n
  induction n with
  | zero => simp [Kc]
  | succ n ih => rw [Kc_succ]; positivity

lemma Kc_pos : ∀ n, 0 < Kc n := by
  intro n
  induction n with
  | zero => simp [Kc]
  | succ n ih => rw [Kc_succ]; positivity

lemma Kc_le_succ (n : ℕ) : Kc n ≤ Kc (n + 1) := by
  rw [Kc_succ]
  have h1 : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  nlinarith [Kc_nonneg n]

lemma Kc_mono : Monotone Kc := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact ih.trans (Kc_le_succ m)

/-- Elementary: `x/a + 1 ≤ 2 (x/b + 1)` when `0 ≤ x`, `a,b > 0` and `b/2 ≤ a`. -/
lemma div_add_one_le_two {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b) (hab : b / 2 ≤ a) :
    x / a + 1 ≤ 2 * (x / b + 1) := by
  have h2 : x / a ≤ x / (b / 2) := div_le_div_of_nonneg_left hx (half_pos hb) hab
  have h3 : x / (b / 2) = 2 * (x / b) := by field_simp
  rw [h3] at h2
  linarith

/-- The peeled presentation evaluated at a real vector is the orthogonal projection of
`D.Φ (∑ j, t j • v j)` onto the orthogonal complement of `D.p`. -/
lemma recStep_eq_projU {R : ℕ} (D : RecData R ι) (t : Fin (R - 1) → ℝ) :
    D.step t = projU D.p (D.Φ (∑ j, t j • (fun k => (D.v j k : ℝ)))) := by
  rw [RecData.step]
  show latStep D.Φ D.u D.v t = _
  rw [latStep_apply]
  rw [map_sum D.Φ (fun j => t j • (fun k => (D.v j k : ℝ))) Finset.univ]
  rw [map_sum (projU D.p) (fun j => D.Φ (t j • (fun k => (D.v j k : ℝ)))) Finset.univ]
  simp only [map_smul, RecData.p]

/-- The shortest vector of a `RecData` is nonzero. -/
lemma recStep_p_ne_zero {R : ℕ} (D : RecData R ι) : D.p ≠ 0 := by
  intro h0
  have h1 : (fun j => (D.u j : ℝ)) = 0 := by
    apply D.Φ_inj
    rw [map_zero]
    exact h0
  exact D.u_ne (funext fun j => Int.cast_eq_zero.mp (congr_fun h1 j))

/-- The peeled presentation is injective. -/
lemma recStep_injective {R : ℕ} (D : RecData R ι) : Function.Injective D.step := by
  have hp : D.p ≠ 0 := recStep_p_ne_zero D
  intro t t' h
  set s : Fin (R - 1) → ℝ := t - t' with hs
  set w : Fin R → ℝ := ∑ j, s j • (fun k => (D.v j k : ℝ)) with hw
  have hs0 : D.step s = 0 := by rw [hs, map_sub, h, sub_self]
  have hstep : D.step s = projU D.p (D.Φ w) := by
    rw [recStep_eq_projU D s, ← hw]
  have hproj : projU D.p (D.Φ w) = 0 := by rw [← hstep]; exact hs0
  obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp
    ((projU_eq_zero_iff D.p hp (D.Φ w)).mp hproj)
  have hu : w = mu • (fun j => (D.u j : ℝ)) := by
    have h2 : w - mu • (fun j => (D.u j : ℝ)) = 0 := by
      apply D.Φ_inj
      rw [map_zero, map_sub, map_smul, ← RecData.p, hmu, sub_self]
    exact sub_eq_zero.mp h2
  have hdep : (-mu, s) = 0 := by
    apply D.indep
    show (-mu) • (fun j => (D.u j : ℝ)) + ∑ i, s i • (fun j => (D.v i j : ℝ)) = 0
    have hsum : ∑ i, s i • (fun j => (D.v i j : ℝ)) = mu • (fun j => (D.u j : ℝ)) := by
      rw [← hw]; exact hu
    rw [hsum, neg_smul, neg_add_cancel]
  have hsc : s = 0 := by
    have := congrArg Prod.snd hdep
    simpa using this
  exact sub_eq_zero.mp (by rw [← hs]; exact hsc)

/-- Schmidt's bound in coefficient space: for an injective presentation `Φ` of a rank-`R`
lattice, the number of lattice points of norm at most `T ≥ 1` is at most
`Kc R · ∏_{i=1}^{R} (T / λ_i + 1)`. -/
theorem latCount_bound : ∀ R : ℕ, ∀ (Φ : LatMap (ι := ι) R), Function.Injective Φ →
    ∀ T : ℝ, 1 ≤ T →
    (latCount Φ T : ℝ) ≤ Kc R * ∏ i ∈ Finset.range R, (T / latMin Φ (i + 1) + 1) := by
  intro R
  induction R with
  | zero =>
      intro Φ hΦ T hT
      have hcard : latCount Φ T = 1 := by
        rw [latCount, latSet]
        have huniv : {t : Fin 0 → ℤ | ‖Φ (fun i => (t i : ℝ))‖ ≤ T} = Set.univ := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          have h0 : (fun i => (t i : ℝ)) = 0 := funext fun i => Fin.elim0 i
          rw [h0, map_zero, norm_zero]
          linarith
        rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
        simp
      rw [hcard]
      simp [Kc]
  | succ n ih =>
      intro Φ hΦ T hT
      have hT0 : (0:ℝ) ≤ T := by linarith
      have hR : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hlampos : 0 < latMin Φ 1 := gon_latMin_pos Φ hΦ le_rfl hR
      have hAnn : 0 ≤ 2 * T / latMin Φ 1 + 1 := by
        have : 0 ≤ 2 * T / latMin Φ 1 := div_nonneg (by linarith) hlampos.le
        linarith
      obtain ⟨u, hu_ne, hu_prim, hu_min⟩ := lat_min_attained hR Φ hΦ
      obtain ⟨v, hv_bij, hv_indep⟩ := primBasisGen hR u hu_prim
      let D : RecData (n + 1) ι := ⟨Φ, u, v, hΦ, hu_ne, hu_prim, hv_bij, hv_indep⟩
      have hDp : D.p = Φ (fun j => (u j : ℝ)) := rfl
      have hDΦ : D.Φ = Φ := rfl
      have hDmin : ∀ j, 1 ≤ j → latMin Φ (j + 1) / 2 ≤ latMin D.step j := by
        intro j hj
        exact latStep_min D (by rw [hDp, hDΦ]; exact hu_min) hj
      have hstep_inj : Function.Injective D.step := recStep_injective D
      have hcount : (latCount Φ T : ℝ) ≤ (2 * T / latMin Φ 1 + 1) * (latCount D.step T : ℝ) := by
        have h1 := latStep_count D hT0
        rw [hDp, hDΦ, hu_min] at h1
        exact h1
      have ihh : (latCount D.step T : ℝ) ≤
          Kc n * ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1) :=
        ih D.step hstep_inj T hT
      have hpt : ∀ i ∈ Finset.range n,
          T / latMin D.step (i + 1) + 1 ≤ 2 * (T / latMin Φ (i + 2) + 1) := by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have ha : 0 < latMin D.step (i + 1) :=
          gon_latMin_pos D.step hstep_inj (by omega) (by omega)
        have hb : 0 < latMin Φ (i + 2) := gon_latMin_pos Φ hΦ (by omega) (by omega)
        have hmin : latMin Φ (i + 2) / 2 ≤ latMin D.step (i + 1) := by
          have h2 := hDmin (i + 1) (by omega)
          simpa using h2
        exact div_add_one_le_two hT0 ha hb hmin
      have hprod : ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1)
          ≤ 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
        calc ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1)
            ≤ ∏ i ∈ Finset.range n, (2 * (T / latMin Φ (i + 2) + 1)) :=
              Finset.prod_le_prod₀ (fun i hi => by
                have hi' : i < n := Finset.mem_range.mp hi
                have hpos : 0 < latMin D.step (i + 1) :=
                  gon_latMin_pos D.step hstep_inj (by omega) (by omega)
                have : 0 ≤ T / latMin D.step (i + 1) := div_nonneg hT0 hpos.le
                linarith) hpt
          _ = 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      have hsplit : ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1)
          = (T / latMin Φ 1 + 1) * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
        rw [Finset.prod_range_succ', mul_comm]
      have hQnn : 0 ≤ ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1) :=
        Finset.prod_nonneg fun i hi => by
          have hi' : i < n := Finset.mem_range.mp hi
          have hpos : 0 < latMin D.step (i + 1) :=
            gon_latMin_pos D.step hstep_inj (by omega) (by omega)
          have : 0 ≤ T / latMin D.step (i + 1) := div_nonneg hT0 hpos.le
          linarith
      have hPnn : 0 ≤ ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) :=
        Finset.prod_nonneg fun i hi => by
          have hi' : i < n := Finset.mem_range.mp hi
          have hpos : 0 < latMin Φ (i + 2) := gon_latMin_pos Φ hΦ (by omega) (by omega)
          have : 0 ≤ T / latMin Φ (i + 2) := div_nonneg hT0 hpos.le
          linarith
      have hA : 2 * T / latMin Φ 1 + 1 ≤ 2 * (T / latMin Φ 1 + 1) := by
        have : 2 * T / latMin Φ 1 = 2 * (T / latMin Φ 1) := by ring
        linarith
      have key : (2 * T / latMin Φ 1 + 1)
            * (Kc n * ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1))
          ≤ Kc (n + 1) * ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1) := by
        rw [hsplit, Kc_succ, pow_succ]
        have hfac : 0 ≤ Kc n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) :=
          mul_nonneg (mul_nonneg (Kc_nonneg n) (by positivity)) hPnn
        have h1 : (2 * T / latMin Φ 1 + 1)
              * (Kc n * ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1))
            ≤ (2 * T / latMin Φ 1 + 1)
              * (Kc n * (2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hAnn
          exact mul_le_mul_of_nonneg_left hprod (Kc_nonneg n)
        refine h1.trans ?_
        have h2 : (2 * T / latMin Φ 1 + 1)
              * (Kc n * (2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1)))
            = (Kc n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * T / latMin Φ 1 + 1) := by ring
        rw [h2]
        have h3 : (Kc n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * T / latMin Φ 1 + 1)
            ≤ (Kc n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * (T / latMin Φ 1 + 1)) :=
          mul_le_mul_of_nonneg_left hA hfac
        refine h3.trans ?_
        exact le_of_eq (by ring)
      calc (latCount Φ T : ℝ)
          ≤ (2 * T / latMin Φ 1 + 1) * (latCount D.step T : ℝ) := hcount
        _ ≤ (2 * T / latMin Φ 1 + 1)
              * (Kc n * ∏ i ∈ Finset.range n, (T / latMin D.step (i + 1) + 1)) :=
              mul_le_mul_of_nonneg_left ihh hAnn
        _ ≤ Kc (n + 1) * ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1) := key

/-- **Schmidt's bound** for lattice points in a Euclidean ball:
`#(L ∩ B(T)) ≤ K · ∏_{i=1}^{rk L} (T/λ_i(L) + 1)` with `K` depending only on `ι`. -/
theorem schmidt_bound {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := by
  classical
  refine ⟨Kc (Fintype.card ι), Kc_pos _, ?_⟩
  intro L T hT
  haveI : Module.Finite ℤ L := inferInstance
  let b : Module.Basis (Fin (rk L)) ℤ L := Module.finBasis ℤ L
  have hv : LinearIndependent ℤ (vb (L := L) b) :=
    b.linearIndependent.map' (Submodule.subtype L)
      (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
  have hΦ : Function.Injective (phiOf (vb (L := L) b)) := phiOf_injective _ hv
  have hbound := latCount_bound (rk L) (phiOf (vb (L := L) b)) hΦ T hT
  have hbc : (ballCount L T : ℝ) = (latCount (phiOf (vb (L := L) b)) T : ℝ) := by
    rw [ballCount_eq_latCount b T]
  rw [hbc]
  have hLprod : ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)
      = ∏ i ∈ Finset.range (rk L), (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [lam_eq_latMin b (i + 1)]
  rw [hLprod]
  calc (latCount (phiOf (vb (L := L) b)) T : ℝ)
      ≤ Kc (rk L) * ∏ i ∈ Finset.range (rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := hbound
    _ ≤ Kc (Fintype.card ι) * ∏ i ∈ Finset.range (rk L),
          (T / latMin (phiOf (vb (L := L) b)) (i + 1) + 1) := by
        refine mul_le_mul_of_nonneg_right (Kc_mono (rk_le_card L)) ?_
        exact Finset.prod_nonneg (fun i hi => by
          have hi' : i < rk L := Finset.mem_range.mp hi
          have : 0 < latMin (phiOf (vb (L := L) b)) (i + 1) :=
            gon_latMin_pos _ hΦ (by omega) (by omega)
          exact add_nonneg (div_nonneg (by linarith) this.le) zero_le_one)

end Work.HP.FM
