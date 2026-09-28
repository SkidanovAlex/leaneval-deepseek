import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.GonLib
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.phiOf_injective
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.numaux.lam_le_iff
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.FM.latStep_injective
import Submission.Work.HP.Sig2.prim_completion
import Submission.Work.HP.Sig2.latMin_latStep
import Submission.Work.HP.Sig2.latCovol_latStep

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace Work.HP.Sig2

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Transfer between a submodule of `ℤ^ι` and its coefficient presentation -/

/-- The underlying integer vectors of a `ℤ`-basis of `L`. -/
abbrev vbB {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) (i : Fin R) : ι → ℤ :=
  (b i : ι → ℤ)

/-- The `ℤ`-linear map `t ↦ Σ i, t i • b i` from coefficients to `ℤ^ι`. -/
noncomputable def latEmbB {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) :
    (Fin R → ℤ) →ₗ[ℤ] (ι → ℤ) :=
  (Submodule.subtype L).comp b.equivFun.symm.toLinearMap

theorem latEmbB_apply {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L)
    (t : Fin R → ℤ) : latEmbB b t = ∑ i, t i • vbB b i := by
  show ((b.equivFun.symm t : L) : ι → ℤ) = _
  rw [Module.Basis.equivFun_symm_apply]
  exact (map_sum (Submodule.subtype L) (fun i => t i • b i) Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => by rw [map_smul, vbB, Submodule.coe_subtype])

theorem latEmbB_equivFun {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L)
    (x : L) : latEmbB b (b.equivFun x) = (x : ι → ℤ) := by
  show ((b.equivFun.symm (b.equivFun x) : L) : ι → ℤ) = (x : ι → ℤ)
  rw [LinearEquiv.symm_apply_apply]

theorem latEmbB_injective {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) :
    Function.Injective (latEmbB b) := by
  intro x y h
  exact b.equivFun.symm.injective (Subtype.coe_injective h)

theorem vbB_linIndep {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) :
    LinearIndependent ℤ (vbB b) := by
  have h := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  simpa [vbB, Function.comp_def] using h

theorem phiOf_vbB_injective {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) :
    Function.Injective (phiOf (vbB b)) :=
  phiOf_injective (vbB b) (vbB_linIndep b)

theorem latEmbB_norm {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L)
    (t : Fin R → ℤ) : ‖phiOf (vbB b) (fun i => (t i : ℝ))‖ = eNorm (latEmbB b t) := by
  rw [latEmbB_apply, phiOf_norm]

/-- The successive minima of `L` are the successive minima of the coefficient lattice. -/
theorem lam_eq_latMin_b {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L)
    (i : ℕ) : lam L i = latMin (phiOf (vbB b)) i := by
  rw [lam, latMin]
  congr 1
  ext r
  constructor
  · rintro ⟨hr, f, hfL, hfind, hfr⟩
    set g : Fin i → (Fin R → ℤ) := fun j => b.equivFun ⟨f j, hfL j⟩ with hg
    have hcomp : (latEmbB b) ∘ g = f := by
      funext j
      rw [Function.comp_apply, hg, latEmbB_equivFun]
    refine ⟨hr, g, ?_, fun j => ?_⟩
    · refine LinearIndependent.of_comp (latEmbB b) ?_
      rw [hcomp]; exact hfind
    · rw [latEmbB_norm b (g j), hg, latEmbB_equivFun]
      exact hfr j
  · rintro ⟨hr, g, hgind, hgr⟩
    refine ⟨hr, (fun j => latEmbB b (g j)), fun j => (b.equivFun.symm (g j) : L).2, ?_, fun j => ?_⟩
    · exact LinearIndependent.map' hgind (latEmbB b)
        (LinearMap.ker_eq_bot.mpr (latEmbB_injective b))
    · rw [← latEmbB_norm b (g j)]
      exact hgr j

theorem inner_toLpB (f g : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 f) (WithLp.toLp 2 g) = ∑ k, f k * g k := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, RCLike.inner_apply]
    simpa using mul_comm (g k) (f k)

theorem phiOf_singleB {R : ℕ} (v : Fin R → (ι → ℤ)) (i : Fin R) :
    phiOf v (Pi.single i (1 : ℝ)) = WithLp.toLp 2 (fun k => ((v i) k : ℝ)) := by
  rw [← WithLp.toLp_ofLp (p := 2) (phiOf v (Pi.single i (1 : ℝ)))]
  congr 1
  funext k
  rw [WithLp.ofLp_toLp, phiOf_apply]
  simp [Pi.single_apply]

/-- `detL` of `L` is the covolume of the coefficient presentation attached to any `ℤ`-basis. -/
theorem detL_eq_latCovol_b {L : Submodule ℤ (ι → ℤ)} {R : ℕ} (b : Module.Basis (Fin R) ℤ L) :
    detL L = latCovol (phiOf (vbB b)) := by
  rw [latCovol, Work.HP.Lat.detL_basis_gram L b]
  congr 1
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    phiOf_singleB, phiOf_singleB, inner_toLpB]

/-! ## Numeric helpers -/

lemma latCovol_zero (Φ : LatMap (ι := ι) 0) : latCovol Φ = 1 := by
  rw [latCovol, Matrix.det_fin_zero, Real.sqrt_one]

lemma latCovol_nonneg {R : ℕ} (Φ : LatMap (ι := ι) R) : 0 ≤ latCovol Φ := Real.sqrt_nonneg _

lemma latMin_nonneg {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : 0 ≤ latMin Φ i := by
  rw [latMin]
  by_cases h : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ r} : Set ℝ).Nonempty
  · exact le_csInf h fun r hr => hr.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- The constant of the recursion: `Kc 0 = 1`, `Kc (n+1) = 2^n * Kc n`. -/
def Kc : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 2 ^ n * Kc n

lemma Kc_succ (n : ℕ) : Kc (n + 1) = 2 ^ n * Kc n := rfl

lemma Kc_pos : ∀ n, 0 < Kc n := by
  intro n
  induction n with
  | zero => norm_num [Kc]
  | succ n ih => rw [Kc_succ]; positivity

lemma Kc_nonneg (n : ℕ) : 0 ≤ Kc n := (Kc_pos n).le

lemma Kc_le_succ (n : ℕ) : Kc n ≤ Kc (n + 1) := by
  rw [Kc_succ]
  have h : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith [Kc_nonneg n]

lemma Kc_mono {m n : ℕ} (h : m ≤ n) : Kc m ≤ Kc n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      calc Kc m ≤ Kc (m + k) := ih
        _ ≤ Kc (m + k + 1) := Kc_le_succ (m + k)
        _ = Kc (m + (k + 1)) := by rw [Nat.add_assoc]

lemma rk_le_card (L : Submodule ℤ (ι → ℤ)) : rk L ≤ Fintype.card ι := by
  have h1 : Module.finrank ℤ L ≤ Module.finrank ℤ (ι → ℤ) := Submodule.finrank_le L
  rw [Module.finrank_pi] at h1
  exact h1

/-! ## The one-step recursion (assembled from the delegated pieces) -/

theorem lat_recursion_via {R : ℕ} (hR : 1 ≤ R)
    (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) :
    ∃ (Ψ : LatMap (ι := ι) (R - 1)) (x₀ : EuclideanSpace ℝ ι),
      Function.Injective Ψ ∧ latMin Φ 1 = ‖x₀‖ ∧
      (∀ j : ℕ, 1 ≤ j → latMin Φ (j + 1) ≤ 2 * latMin Ψ j) ∧
      latCovol Φ = ‖x₀‖ * latCovol Ψ := by
  obtain ⟨u, hu0, hup, hu⟩ := Work.HP.lat_min_attained hR Φ hΦ
  obtain ⟨v, hbij, hind⟩ := prim_completion hR u hup
  let D : Work.HP.FM.RecData R ι :=
    { Φ := Φ, u := u, v := v, Φ_inj := hΦ, u_ne := hu0, u_prim := hup, bij := hbij,
      indep := hind }
  refine ⟨D.step, D.p, Work.HP.FM.latStep_injective D, ?_, ?_, ?_⟩
  · change latMin Φ 1 = ‖Φ (fun j => (u j : ℝ))‖
    rw [hu]
  · intro j hj
    have h := latMin_latStep hR Φ hΦ u v hbij hu j hj
    simpa only [Work.HP.FM.RecData.step] using h
  · have h := latCovol_latStep hR Φ hΦ u v hbij
    simpa only [Work.HP.FM.RecData.step, Work.HP.FM.RecData.p] using h

lemma prod_range_eq_zero_mul {R : ℕ} (hpos : 0 < R) (g : ℕ → ℝ) :
    (∏ j ∈ Finset.range R, g j) = g 0 * ∏ i ∈ Finset.range (R - 1), g (i + 1) := by
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
  rw [Finset.prod_range_succ', mul_comm, Nat.pred_eq_sub_one]

/-! ## Minkowski's second theorem for coefficient lattices -/

theorem latMap_minkowski_aux : ∀ (R : ℕ) (Φ : LatMap (ι := ι) R), Function.Injective Φ →
    (∏ j ∈ Finset.range R, latMin Φ (j + 1)) ≤ Kc R * latCovol Φ := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    intro Φ hΦ
    rcases Nat.eq_zero_or_pos R with h0 | hpos
    · subst h0
      simp [Kc, latCovol_zero]
    · obtain ⟨Ψ, x₀, hΨinj, hmin1, hminj, hcov⟩ := lat_recursion_via hpos Φ hΦ
      have hKc : Kc R = 2 ^ (R - 1) * Kc (R - 1) := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
        rw [Kc_succ, Nat.pred_eq_sub_one]
      have hPg : (∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1)) ≤ Kc (R - 1) * latCovol Ψ :=
        ih (R - 1) (by omega) Ψ hΨinj
      have hsplit : (∏ j ∈ Finset.range R, latMin Φ (j + 1))
          = latMin Φ 1 * ∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2) :=
        prod_range_eq_zero_mul hpos (fun j => latMin Φ (j + 1))
      rw [hsplit]
      have hstep1 : (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
          ≤ 2 ^ (R - 1) * ∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1) := by
        calc (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
            ≤ ∏ j ∈ Finset.range (R - 1), (2 * latMin Ψ (j + 1)) := by
              refine Finset.prod_le_prod₀ (fun j _ => latMin_nonneg Φ _) (fun j _ => ?_)
              have h := hminj (j + 1) (by omega)
              rw [show j + 1 + 1 = j + 2 from by omega] at h
              exact h
          _ = 2 ^ (R - 1) * ∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      have hstep2 : 2 ^ (R - 1) * (∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1))
          ≤ 2 ^ (R - 1) * (Kc (R - 1) * latCovol Ψ) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      calc latMin Φ 1 * (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
          ≤ latMin Φ 1 * (2 ^ (R - 1) * (Kc (R - 1) * latCovol Ψ)) :=
            mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (latMin_nonneg Φ 1)
        _ = Kc R * latCovol Φ := by rw [hmin1, hcov, hKc]; ring

theorem minkowski_prod {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ L : Submodule ℤ (ι → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := by
  refine ⟨Kc (Fintype.card ι), Kc_pos _, fun L => ?_⟩
  obtain ⟨n, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = rk L := by
    show n = Module.finrank ℤ L
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  let b : Module.Basis (Fin (rk L)) ℤ L := b0.reindex (finCongr hn)
  have hΦ : Function.Injective (phiOf (vbB b)) := phiOf_vbB_injective b
  have hprod : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
      = ∏ j ∈ Finset.range (rk L), latMin (phiOf (vbB b)) (j + 1) :=
    Finset.prod_congr rfl fun j _ => lam_eq_latMin_b b (j + 1)
  rw [hprod]
  have hmain := latMap_minkowski_aux (rk L) (phiOf (vbB b)) hΦ
  rw [detL_eq_latCovol_b b]
  calc (∏ j ∈ Finset.range (rk L), latMin (phiOf (vbB b)) (j + 1))
      ≤ Kc (rk L) * latCovol (phiOf (vbB b)) := hmain
    _ ≤ Kc (Fintype.card ι) * latCovol (phiOf (vbB b)) :=
        mul_le_mul_of_nonneg_right (Kc_mono (rk_le_card L)) (latCovol_nonneg _)

end Work.HP.Sig2
