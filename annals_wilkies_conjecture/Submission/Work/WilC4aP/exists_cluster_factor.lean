import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg
import Submission.Work.WilC4aP.analyticAt_Pz_eval
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Main
import Submission.Work.WilC4aP.exactOrder_shifted_eval
import Submission.Work.WilC4aP.exists_box_of_eventually_ambient
import Submission.Work.WilC4aP.exists_monic_factor_of_le
import Submission.Work.WilC4aP.norm_root_lt_of_coeffs_le

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open Polynomial

namespace Work.WilC4aP

/-! ## The prepared polynomial over an arbitrary coefficient ring -/

/-- `X^k + Σ_{i<k} A i * X^i`, the Weierstrass polynomial with coefficient vector `A`. -/
def prepPoly {R : Type*} [CommSemiring R] (k : ℕ) (A : Fin k → R) : Polynomial R :=
  X ^ k + ∑ i : Fin k, C (A i) * X ^ (i : ℕ)

lemma prepPoly_coeff_self {R : Type*} [CommSemiring R] {k : ℕ} (A : Fin k → R) :
    (prepPoly k A).coeff k = 1 := by
  rw [prepPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow_self, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_zero]
  · simp
  · intro x _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_gt x.isLt), mul_zero]

lemma prepPoly_coeff_fin {R : Type*} [CommSemiring R] {k : ℕ} (A : Fin k → R) (i : Fin k) :
    (prepPoly k A).coeff (i : ℕ) = A i := by
  rw [prepPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  have h1 : (X ^ k : Polynomial R).coeff (i : ℕ) = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt)]
  rw [h1, zero_add, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
  · intro x _ hx
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (Fin.val_ne_of_ne (Ne.symm hx)), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma prepPoly_coeff_of_lt {R : Type*} [CommSemiring R] {k n : ℕ} (A : Fin k → R) (hn : k < n) :
    (prepPoly k A).coeff n = 0 := by
  rw [prepPoly, Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  have h1 : (X ^ k : Polynomial R).coeff n = 0 := by
    rw [Polynomial.coeff_X_pow, if_neg (Nat.ne_of_gt hn)]
  rw [h1, zero_add, Finset.sum_eq_zero]
  intro x _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (Nat.ne_of_gt (lt_trans x.isLt hn)), mul_zero]

lemma prepPoly_eval {R : Type*} [CommSemiring R] (k : ℕ) (A : Fin k → R) (w : R) :
    (prepPoly k A).eval w = w ^ k + ∑ i : Fin k, A i * w ^ (i : ℕ) := by
  simp only [prepPoly, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

lemma prepPoly_natDegree {R : Type*} [CommSemiring R] [Nontrivial R] (k : ℕ) (A : Fin k → R) :
    (prepPoly k A).natDegree = k := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    exact fun n hn => prepPoly_coeff_of_lt A hn
  · rw [prepPoly_coeff_self]
    exact one_ne_zero

lemma prepPoly_monic {R : Type*} [CommSemiring R] [Nontrivial R] (k : ℕ) (A : Fin k → R) :
    (prepPoly k A).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, prepPoly_natDegree k A, prepPoly_coeff_self]

/-! ## Coefficients of a composition with `X - C c` -/

lemma coeff_comp_eq {R : Type*} [CommSemiring R] (p q : Polynomial R) (n : ℕ) :
    (p.comp q).coeff n = ∑ i ∈ p.support, p.coeff i * (q ^ i).coeff n := by
  have hp : p = ∑ i ∈ p.support, C (p.coeff i) * X ^ i := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum_def]
  conv_lhs => rw [hp]
  rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, Polynomial.coeff_C_mul]

lemma coeff_comp_X_sub_C_const (p : Polynomial (ℂ → ℂ)) (c : ℂ) (n : ℕ) :
    (p.comp (X - C (cstHom c))).coeff n
      = ∑ i ∈ p.support, p.coeff i * (fun _ : ℂ => ((X - C c : Polynomial ℂ) ^ i).coeff n) := by
  rw [coeff_comp_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hmap : (X - C (cstHom c) : Polynomial (ℂ → ℂ)) = (X - C c : Polynomial ℂ).map cstHom := by
    simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hmap, ← Polynomial.map_pow, Polynomial.coeff_map]
  rfl

lemma holCoeffs_comp_X_sub_C_const {p : Polynomial (ℂ → ℂ)} (hp : HolCoeffs p 0) (c : ℂ) :
    HolCoeffs (p.comp (X - C (cstHom c))) 0 := by
  intro n
  rw [coeff_comp_X_sub_C_const]
  exact Finset.analyticAt_sum _ fun i _ => (hp i).mul analyticAt_const

/-- The `z`-fibre of `prepPoly` is the prepared polynomial with coefficients `A i z`. -/
lemma Pz_prepPoly (k : ℕ) (A : Fin k → ℂ → ℂ) (z : ℂ) :
    Pz (prepPoly k A) z = prepPoly k (fun i => A i z) := by
  simp only [Pz, prepPoly, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, evAt_apply]

/-! ## The local factor lemma

If a polynomial `R` agrees on a disc containing all roots of a monic `G` with `G` times a
function continuous at those roots, then `R` vanishes (the roots of `G` are roots of `R` with
at least their multiplicity, forcing `G ∣ R` and contradicting the degree bound). -/

theorem local_factor_eq_zero {G R : Polynomial ℂ} {V : ℂ → ℂ} {c : ℂ} {σ : ℝ}
    (hσ : 0 < σ) (hG : G.Monic) (hR : R.natDegree < G.natDegree)
    (hV : ∀ β ∈ G.roots, ContinuousAt V β)
    (hroots : ∀ β ∈ G.roots, β ∈ Metric.ball c σ)
    (hide : ∀ w ∈ Metric.ball c σ, R.eval w = G.eval w * V w) : R = 0 := by
  by_cases hR0 : R = 0
  · exact hR0
  · exfalso
    -- the multiplicity of every root of `G` in `R` is at least its multiplicity in `G`
    have hmul : ∀ β ∈ G.roots, G.rootMultiplicity β ≤ R.rootMultiplicity β := by
      intro β hβ
      obtain ⟨G₁, hG1, hG₁⟩ :=
        Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd G hG.ne_zero β
      obtain ⟨R₁, hR1, hR₁⟩ :=
        Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd R hR0 β
      have hG₁ne : G₁.eval β ≠ 0 :=
        fun h => hG₁ ((Polynomial.dvd_iff_isRoot).mpr h)
      have hR₁ne : R₁.eval β ≠ 0 :=
        fun h => hR₁ ((Polynomial.dvd_iff_isRoot).mpr h)
      by_contra hcon
      push_neg at hcon
      have hβball : β ∈ Metric.ball c σ := hroots β hβ
      -- the identity `R₁ = (· - β) ^ (m - j) * (G₁ * V)` near `β`
      have hkey : ∀ w ∈ Metric.ball c σ, w ≠ β →
          R₁.eval w = (w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β) *
            (G₁.eval w * V w) := by
        intro w hw hwne
        have hRval : R.eval w = (w - β) ^ (R.rootMultiplicity β) * R₁.eval w := by
          conv_lhs => rw [hR1]
          simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
        have hGval : G.eval w = (w - β) ^ (G.rootMultiplicity β) * G₁.eval w := by
          conv_lhs => rw [hG1]
          simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
        have h3 : R.eval w = G.eval w * V w := hide w hw
        have hmj : (w - β) ^ (G.rootMultiplicity β)
            = (w - β) ^ (R.rootMultiplicity β)
              * (w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β) := by
          rw [← pow_add]
          congr 1
          omega
        have h4 : (w - β) ^ (R.rootMultiplicity β) * R₁.eval w
            = (w - β) ^ (R.rootMultiplicity β) *
              ((w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β)
                * (G₁.eval w * V w)) := by
          rw [← hRval, h3, hGval, hmj]
          ring
        exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hwne)) h4
      -- pass to the limit in the punctured neighbourhood of `β`
      have hlim1 : Tendsto (fun w : ℂ => R₁.eval w) (𝓝[≠] β) (𝓝 (R₁.eval β)) :=
        ((Polynomial.continuous R₁).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      have hlim2 : Tendsto
          (fun w : ℂ => (w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β)
            * (G₁.eval w * V w)) (𝓝[≠] β) (𝓝 0) := by
        have hbase : Tendsto (fun w : ℂ => w - β) (𝓝 β) (𝓝 0) := by
          simpa using (tendsto_id.sub tendsto_const_nhds :
            Tendsto (fun w : ℂ => w - β) (𝓝 β) (𝓝 (β - β)))
        have hpow : Tendsto (fun w : ℂ => (w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β))
            (𝓝 β) (𝓝 0) := by
          simpa [zero_pow (by omega :
            G.rootMultiplicity β - R.rootMultiplicity β ≠ 0)] using
            hbase.pow (G.rootMultiplicity β - R.rootMultiplicity β)
        have hGV : ContinuousAt (fun w : ℂ => G₁.eval w * V w) β :=
          ((Polynomial.continuous G₁).continuousAt).mul (hV β hβ)
        have h1 : Tendsto (fun w : ℂ => (w - β) ^
            (G.rootMultiplicity β - R.rootMultiplicity β)) (𝓝[≠] β) (𝓝 0) :=
          hpow.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun w : ℂ => G₁.eval w * V w) (𝓝[≠] β)
            (𝓝 (G₁.eval β * V β)) :=
          hGV.tendsto.mono_left nhdsWithin_le_nhds
        have h := h1.mul h2
        rw [zero_mul] at h
        exact h
      have hev : (fun w : ℂ => R₁.eval w) =ᶠ[𝓝[≠] β]
          (fun w : ℂ => (w - β) ^ (G.rootMultiplicity β - R.rootMultiplicity β)
            * (G₁.eval w * V w)) := by
        rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
        filter_upwards [Metric.isOpen_ball.mem_nhds hβball] with w hw hwne
        exact hkey w hw hwne
      exact hR₁ne (tendsto_nhds_unique (hlim1.congr' hev) hlim2)
    -- hence `G` divides `R`, contradicting the degree hypothesis
    have hle : G.roots ≤ R.roots := by
      rw [Multiset.le_iff_count]
      intro β
      by_cases hβ : β ∈ G.roots
      · rw [Polynomial.count_roots, Polynomial.count_roots]
        exact hmul β hβ
      · rw [Multiset.count_eq_zero_of_notMem hβ]
        exact Nat.zero_le _
    have hdvd : G ∣ R := by
      rw [← prod_roots_eq_of_monic hG]
      exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hR0 G.roots).mpr hle
    have := natDegree_le_of_dvd hdvd hR0
    omega

/-! ## The local cluster divisor -/

/-- Weierstrass preparation for a polynomial with holomorphic coefficients gives a local
factorization of the fibre polynomial along the cluster of a root of the reduction. -/
lemma exists_local_cluster_divisor (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (han : HolCoeffs P 0) {α : ℂ} {k : ℕ}
    (hroot : (Pz P 0).rootMultiplicity α = k) (hk : 0 < k) :
    ∃ G : Polynomial (ℂ → ℂ), HolCoeffs G 0 ∧ Pz G 0 = (X - C α) ^ k ∧
      (∀ z, (Pz G z).Monic ∧ (Pz G z).natDegree = k) ∧
      ∀ᶠ z in 𝓝 0, Pz G z ∣ Pz P z := by
  -- ## Step 1: the shifted slice, its analyticity and exact order
  set f : (Fin 1 → ℂ) × ℂ → ℂ := fun x => (Pz P (x.1 0)).eval (x.2 + α) with hfdef
  have hf : AnalyticAt ℂ f 0 := by
    have h1 : AnalyticAt ℂ (fun p : ℂ × ℂ => (Pz P p.1).eval p.2) (0, α) :=
      analyticAt_Pz_eval P han α
    have h2 : AnalyticAt ℂ (fun x : (Fin 1 → ℂ) × ℂ => (x.1 0, x.2 + α)) 0 := by
      refine AnalyticAt.prod ?_ ?_
      · exact AnalyticAt.comp
          (ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj (R := ℂ) 0) _)
          (analyticAt_fst (p := (0 : (Fin 1 → ℂ) × ℂ)))
      · exact analyticAt_snd.add analyticAt_const
    rw [hfdef]
    have h1' : AnalyticAt ℂ (fun p : ℂ × ℂ => (Pz P p.1).eval p.2)
        ((fun x : (Fin 1 → ℂ) × ℂ => (x.1 0, x.2 + α)) 0) := by
      simpa [zero_add] using h1
    exact AnalyticAt.comp (x := (0 : (Fin 1 → ℂ) × ℂ))
      (f := fun x : (Fin 1 → ℂ) × ℂ => (x.1 0, x.2 + α)) h1' h2
  have horder : ClassicalComplexWPT.ExactOrderInLastVariable f k := by
    have h := exactOrder_shifted_eval P hmon hroot
    have hfs : ClassicalComplexWPT.lastSlice f = fun w : ℂ => (Pz P 0).eval (w + α) := by
      rw [hfdef]
      funext w
      simp [ClassicalComplexWPT.lastSlice]
    rw [ClassicalComplexWPT.ExactOrderInLastVariable, hfs]
    exact h
  -- ## Step 2: Weierstrass preparation
  obtain ⟨a, u, hprep, -⟩ :=
    ClassicalComplexWPT.classicalComplexWeierstrassPreparation 1 k f hf horder
  have ha_an : ∀ i, AnalyticAt ℂ (a i) 0 := hprep.1
  have ha0 : ∀ i, a i 0 = 0 := hprep.2.1
  have hu_an : AnalyticAt ℂ u 0 := hprep.2.2.1
  have hfac : f =ᶠ[𝓝 0] fun x => u x * ClassicalComplexWPT.preparedPolynomial k a x :=
    hprep.2.2.2.2
  -- ## Step 3: the prepared polynomial and the cluster factor
  set A : Fin k → ℂ → ℂ := fun i z => a i (fun _ : Fin 1 => z) with hAdef
  have hAan : ∀ i, AnalyticAt ℂ (A i) 0 := by
    intro i
    have hcl : AnalyticAt ℂ (fun z : ℂ => (fun _ : Fin 1 => z)) 0 :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.pi (fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ)) 0
    rw [hAdef]
    exact AnalyticAt.comp (x := (0 : ℂ)) (ha_an i) hcl
  have hA0 : ∀ i, A i 0 = 0 := by
    intro i; rw [hAdef]; exact ha0 i
  set Gw : Polynomial (ℂ → ℂ) := prepPoly k A with hGwdef
  have hGwhol : HolCoeffs Gw 0 := by
    intro n
    rcases lt_or_ge n k with hnk | hnk
    · rw [show Gw.coeff n = A ⟨n, hnk⟩ from by
        rw [hGwdef]; exact prepPoly_coeff_fin A ⟨n, hnk⟩]
      exact hAan ⟨n, hnk⟩
    · rcases eq_or_lt_of_le hnk with h | h
      · rw [show Gw.coeff n = 1 from by rw [hGwdef, ← h]; exact prepPoly_coeff_self A]
        exact analyticAt_const
      · rw [show Gw.coeff n = 0 from by rw [hGwdef]; exact prepPoly_coeff_of_lt A h]
        exact analyticAt_const
  have hGwmon : Gw.Monic := by rw [hGwdef]; exact prepPoly_monic k A
  set Gan : Polynomial (ℂ → ℂ) := Gw.comp (X - C (cstHom α)) with hGandef
  have hGanmon : Gan.Monic := by
    rw [hGandef]; exact hGwmon.comp_X_sub_C (cstHom α)
  have hGanhol : HolCoeffs Gan 0 := by
    rw [hGandef]; exact holCoeffs_comp_X_sub_C_const hGwhol α
  have hPzX : ∀ z : ℂ, Pz (X - C (cstHom α) : Polynomial (ℂ → ℂ)) z = X - C α := by
    intro z
    rw [Pz, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; rfl
  have hGan_eq : ∀ z : ℂ, Pz Gan z = (Pz Gw z).comp (X - C α) := by
    intro z; rw [hGandef, Pz_comp, hPzX]
  have hGw_eval : ∀ z w : ℂ,
      (Pz Gw z).eval w = ClassicalComplexWPT.preparedPolynomial k a ((fun _ : Fin 1 => z), w) := by
    intro z w
    rw [hGwdef, Pz_prepPoly, prepPoly_eval]
    simp only [ClassicalComplexWPT.preparedPolynomial, hAdef]
  have hGan_eval : ∀ z w : ℂ, (Pz Gan z).eval (w + α) = (Pz Gw z).eval w := by
    intro z w
    rw [hGan_eq z, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring_nf
  have hGw0 : Pz Gw 0 = X ^ k := by
    rw [hGwdef, Pz_prepPoly]
    have hzero : (fun i : Fin k => A i 0) = 0 := funext hA0
    rw [hzero, prepPoly]
    simp
  have hGan0 : Pz Gan 0 = (X - C α) ^ k := by
    rw [hGan_eq 0, hGw0, Polynomial.X_pow_comp]
  have hGanfib : ∀ z, (Pz Gan z).Monic ∧ (Pz Gan z).natDegree = k := by
    intro z
    have hfib : Pz Gan z = (prepPoly k (fun i => A i z)).comp (X - C α) := by
      rw [hGan_eq z, hGwdef, Pz_prepPoly]
    refine ⟨?_, ?_⟩
    · rw [hfib]; exact (prepPoly_monic k (fun i => A i z)).comp_X_sub_C α
    · rw [hfib, Polynomial.natDegree_comp, prepPoly_natDegree, Polynomial.natDegree_X_sub_C,
        mul_one]
  -- ## Step 4: the division and the remainder
  set Han : Polynomial (ℂ → ℂ) := P /ₘ Gan with hHandef
  set Ran : Polynomial (ℂ → ℂ) := P %ₘ Gan with hRandef
  have hdiv : Ran + Gan * Han = P := by
    rw [hRandef, hHandef]; exact Polynomial.modByMonic_add_div P Gan
  -- ## Step 5: the two boxes and the coefficient bound
  obtain ⟨ρ₁, σ₁, hρ₁, hσ₁, hbox₁⟩ := exists_box_of_eventually_ambient
    (p := fun x : (Fin 1 → ℂ) × ℂ => f x = u x * ClassicalComplexWPT.preparedPolynomial k a x)
    hfac
  obtain ⟨ρ₂, σ₂, hρ₂, hσ₂, hbox₂⟩ := exists_box_of_eventually_ambient
    (p := fun x : (Fin 1 → ℂ) × ℂ => ContinuousAt u x) hu_an.eventually_continuousAt
  set σM : ℝ := min σ₁ σ₂ with hσMdef
  have hσM : 0 < σM := lt_min hσ₁ hσ₂
  have hσM₁ : σM ≤ σ₁ := min_le_left _ _
  have hσM₂ : σM ≤ σ₂ := min_le_right _ _
  set m : ℝ := min σM (σM ^ k) / (2 * (k : ℝ)) with hmdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkRne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hσpow : 0 < σM ^ k := pow_pos hσM k
  have hSpos : 0 < min σM (σM ^ k) := lt_min hσM hσpow
  have hmpos : 0 < m := by
    rw [hmdef]; exact div_pos hSpos (by positivity)
  have hkm_eq : (k : ℝ) * m = min σM (σM ^ k) / 2 := by
    rw [hmdef]; field_simp
  have hmσ : (k : ℝ) * m < σM := by
    rw [hkm_eq]; linarith [min_le_left σM (σM ^ k)]
  have hmσ' : (k : ℝ) * m < σM ^ k := by
    rw [hkm_eq]; linarith [min_le_right σM (σM ^ k)]
  have hAball : ∀ i : Fin k, ∀ᶠ z in 𝓝 (0 : ℂ), ‖A i z‖ ≤ m := by
    intro i
    have hci : ContinuousAt (A i) 0 := (hAan i).continuousAt
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), A i z ∈ Metric.ball (A i 0) m :=
      hci.eventually_mem (Metric.ball_mem_nhds (A i 0) hmpos)
    filter_upwards [hev] with z hz
    rw [hA0 i] at hz
    exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i, ‖A i z‖ ≤ m := by
    have hfin : ∀ s : Finset (Fin k), ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i ∈ s, ‖A i z‖ ≤ m := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        filter_upwards [hAball i, ih] with z hz hz'
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hz
        · exact hz' j hj
    filter_upwards [hfin Finset.univ] with z hz i
    exact hz i (Finset.mem_univ i)
  obtain ⟨ρ₃, hρ₃pos, hρ₃⟩ := Metric.eventually_nhds_iff.mp hall
  -- ## Step 6: divisibility on a small ball
  have key : ∀ z : ℂ, ‖z‖ < min ρ₁ (min ρ₂ ρ₃) → Pz Gan z ∣ Pz P z := by
    intro z hz
    have hz₁ : ‖z‖ < ρ₁ := lt_of_lt_of_le hz (min_le_left _ _)
    have hz₂ : ‖z‖ < ρ₂ :=
      lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hz₃ : ‖z‖ < ρ₃ :=
      lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
    have hdivz : Pz Ran z + Pz Gan z * Pz Han z = Pz P z := by
      rw [← Pz_mul, ← Pz_add, hdiv]
    -- the local Weierstrass identity on the disk `|Y - α| < σ₁`
    have hlocal : ∀ Y : ℂ, ‖Y - α‖ < σM →
        (Pz Ran z).eval Y = (Pz Gan z).eval Y *
          (u ((fun _ : Fin 1 => z), Y - α) - (Pz Han z).eval Y) := by
      intro Y hY
      have hYeq : Y - α + α = Y := by ring
      have hw1 : (Pz P z).eval Y
          = u ((fun _ : Fin 1 => z), Y - α) * (Pz Gan z).eval Y := by
        have hfY : (Pz P z).eval Y = f ((fun _ : Fin 1 => z), Y - α) := by
          rw [hfdef]; congr 1; ring
        rw [hfY, hbox₁ z (Y - α) hz₁ (lt_of_lt_of_le hY hσM₁)]
        rw [← hGw_eval z (Y - α), ← hGan_eval z (Y - α), hYeq]
      have hw2 : (Pz Ran z).eval Y
          = (Pz P z).eval Y - (Pz Gan z).eval Y * (Pz Han z).eval Y := by
        rw [← hdivz, Polynomial.eval_add, Polynomial.eval_mul]
        ring_nf
      rw [hw2, hw1]; ring_nf
    -- the roots of the fibre factor are the roots of the prepared polynomial in `Y`
    have hroot_of : ∀ β : ℂ, (Pz Gan z).eval β = 0 →
        (prepPoly k (fun i => A i z)).eval (β - α) = 0 := by
      intro β hβ
      have h2 : (Pz Gw z).eval (β - α) = 0 := by
        rw [← hGan_eval z (β - α), show β - α + α = β by ring]
        exact hβ
      rw [hGwdef, Pz_prepPoly] at h2
      exact h2
    have hbound_of : ∀ β : ℂ, (Pz Gan z).eval β = 0 → ‖β - α‖ < σM := by
      intro β hβ
      have h := hroot_of β hβ
      rw [prepPoly] at h
      exact norm_root_lt_of_coeffs_le hk (fun i => A i z) (le_of_lt hmpos) hσM
        (fun i => hρ₃ (by simpa [dist_eq_norm] using hz₃) i) hmσ hmσ' (β - α) h
    have hVcont : ∀ β ∈ (Pz Gan z).roots, ContinuousAt
        (fun Y : ℂ => u ((fun _ : Fin 1 => z), Y - α) - (Pz Han z).eval Y) β := by
      intro β hβ
      have hβroot : (Pz Gan z).eval β = 0 :=
        (Polynomial.mem_roots (hGanfib z).1.ne_zero).mp hβ
      have hβbound : ‖β - α‖ < σM := hbound_of β hβroot
      have hcu : ContinuousAt u (((fun _ : Fin 1 => z) : Fin 1 → ℂ), β - α) :=
        hbox₂ z (β - α) hz₂ (lt_of_lt_of_le hβbound hσM₂)
      have hinner : ContinuousAt (fun Y : ℂ =>
          (((fun _ : Fin 1 => z) : Fin 1 → ℂ), Y - α)) β := by
        have h1 : Tendsto (fun _ : ℂ => (fun _ : Fin 1 => z)) (𝓝 β)
            (𝓝 (fun _ : Fin 1 => z)) := tendsto_const_nhds
        have h2 : Tendsto (fun Y : ℂ => Y - α) (𝓝 β) (𝓝 (β - α)) :=
          tendsto_id.sub tendsto_const_nhds
        exact h1.prodMk_nhds h2
      exact (ContinuousAt.comp (x := β)
        (f := fun Y : ℂ => (((fun _ : Fin 1 => z) : Fin 1 → ℂ), Y - α)) hcu hinner).sub
        ((Polynomial.continuous (Pz Han z)).continuousAt)
    have hroots : ∀ β ∈ (Pz Gan z).roots, β ∈ Metric.ball α σM := by
      intro β hβ
      have hβroot : (Pz Gan z).eval β = 0 :=
        (Polynomial.mem_roots (hGanfib z).1.ne_zero).mp hβ
      rw [Metric.mem_ball, dist_eq_norm]
      exact hbound_of β hβroot
    -- the fibre remainder vanishes
    have hRan_fib : Pz Ran z = (Pz P z) %ₘ (Pz Gan z) := by
      rw [hRandef]; exact Polynomial.map_modByMonic (evAt z) hGanmon
    have hne_one : (Pz Gan z) ≠ 1 := by
      intro hc
      have hn := congrArg Polynomial.natDegree hc
      rw [(hGanfib z).2] at hn
      simp at hn
      omega
    have hnatlt : (Pz Ran z).natDegree < (Pz Gan z).natDegree := by
      rw [hRan_fib]
      exact Polynomial.natDegree_modByMonic_lt (Pz P z) (hGanfib z).1 hne_one
    have hRzero : Pz Ran z = 0 :=
      local_factor_eq_zero hσM (hGanfib z).1 hnatlt hVcont hroots
        (fun Y hY => hlocal Y (by
          rw [Metric.mem_ball, dist_eq_norm] at hY
          exact hY))
    have : Pz P z = Pz Gan z * Pz Han z := by
      rw [← hdivz, hRzero, zero_add]
    exact ⟨Pz Han z, this⟩
  refine ⟨Gan, hGanhol, hGan0, hGanfib, ?_⟩
  have hρ : 0 < min ρ₁ (min ρ₂ ρ₃) := lt_min hρ₁ (lt_min hρ₂ hρ₃pos)
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball 0 (min ρ₁ (min ρ₂ ρ₃)), Metric.ball_mem_nhds 0 hρ, ?_⟩
  intro z hz
  exact key z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

end Work.WilC4aP

namespace Work.WilC4aP

/-- **Analytic Hensel / Weierstrass splitting for `ℂ{z}`.** A monic polynomial with
holomorphic coefficients factors over the holomorphic functions into the cluster over any
root of its reduction: the factor is monic of degree `k` (the multiplicity of `α` in the
reduction) and has the same reduction `(Y - α) ^ k`.

PROOF HINT: the corresponding *formal* factor exists (and is unique) over `ℂ⟦z⟧`; derive it
from Mathlib's Weierstrass preparation result for power series over a complete local ring
(`PowerSeries.exists_isWeierstrassFactorization`; `PowerSeries ℂ` is `(X)`-adically complete),
exactly as in `LeanPool.Puiseux.HenselSplitting` (import `Mathlib.RingTheory.PowerSeries.
WeierstrassPreparation` and `Mathlib.RingTheory.AdicCompletion.Completeness`; the lean-pool
module may be imported directly if it builds, otherwise reproduce its three steps). For the
*convergence* of the formal factor, follow the standard proof of the analytic Weierstrass
preparation result: either (i) the power sums `p r z = (2πi)⁻¹ ∮ w ^ r * P_w / P dw` over a
fixed circle around `α` are holomorphic in `z` (Cauchy's integral formula, differentiation
under the integral sign), and Newton's identities express the coefficients of the cluster
factor as polynomials in `p 0, …, p (k-1)`; or (ii) run Newton iteration in a Banach algebra
of convergent power series with submultiplicative norm, starting from the reduction. -/
theorem exists_cluster_factor {m : ℕ} (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) (han : Work.WilC4aP.HolCoeffs P 0) {α : ℂ} {k : ℕ}
    (hroot : (Work.WilC4aP.Pz P 0).rootMultiplicity α = k) (hk : 0 < k) :
    ∃ G : Polynomial (ℂ → ℂ), G.Monic ∧ G.natDegree = k ∧ Work.WilC4aP.HolCoeffs G 0 ∧
      Work.WilC4aP.Pz G 0 = (Polynomial.X - Polynomial.C α) ^ k ∧
      ∃ H : Polynomial (ℂ → ℂ), H.Monic ∧ P = G * H := by
  obtain ⟨Gan, hGanhol, hGan0, hGanfib, hGandvd⟩ :=
    exists_local_cluster_divisor P hmon han hroot hk
  obtain ⟨V0, hV0mem, hV0⟩ := hGandvd.exists_mem
  have h0V0 : (0 : ℂ) ∈ V0 := mem_of_mem_nhds hV0mem
  -- `k ≤ m`
  have hkm : k ≤ m := by
    have hdvd : (X - C α) ^ k ∣ Pz P 0 := by
      rw [← hroot]; exact Polynomial.pow_rootMultiplicity_dvd _ _
    have hne : (Pz P 0) ≠ 0 := (monic_Pz hmon 0).ne_zero
    have h := natDegree_le_of_dvd hdvd hne
    have hdegk : ((X - C α) ^ k : Polynomial ℂ).natDegree = k := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [hdegk, natDegree_Pz hmon 0, hdeg] at h
    exact h
  have hfac : ∀ z : ℂ, ∃ q : Polynomial ℂ, q.Monic ∧ q.natDegree = k ∧ q ∣ Pz P z := fun z =>
    exists_monic_factor_of_le (monic_Pz hmon z) (by rw [natDegree_Pz hmon z, hdeg]; exact hkm)
  -- the pointwise monic degree-`k` factor of each fibre
  set fac : ℂ → Polynomial ℂ :=
    (fun z => if z ∈ V0 then Pz Gan z else Classical.choose (hfac z)) with hfacdef
  have fac_eq : ∀ z, fac z = if z ∈ V0 then Pz Gan z else Classical.choose (hfac z) := fun z => by
    simp only [hfacdef]
  have fac_monic : ∀ z, (fac z).Monic := fun z => by
    rw [fac_eq z]
    by_cases hz : z ∈ V0
    · rw [if_pos hz]; exact (hGanfib z).1
    · rw [if_neg hz]; exact (Classical.choose_spec (hfac z)).1
  have fac_deg : ∀ z, (fac z).natDegree = k := fun z => by
    rw [fac_eq z]
    by_cases hz : z ∈ V0
    · rw [if_pos hz]; exact (hGanfib z).2
    · rw [if_neg hz]; exact (Classical.choose_spec (hfac z)).2.1
  have fac_dvd : ∀ z, fac z ∣ Pz P z := fun z => by
    rw [fac_eq z]
    by_cases hz : z ∈ V0
    · rw [if_pos hz]; exact hV0 z hz
    · rw [if_neg hz]; exact (Classical.choose_spec (hfac z)).2.2
  -- the global factor, built coefficientwise
  set G : Polynomial (ℂ → ℂ) :=
    (∑ n ∈ Finset.range (k + 1), C (fun z => (fac z).coeff n) * X ^ n) with hGdef
  have G_coeff_le : ∀ n, n ≤ k → G.coeff n = fun z => (fac z).coeff n := by
    intro n hn
    rw [hGdef, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hmiss
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hmiss
  have G_coeff_gt : ∀ n, k < n → G.coeff n = 0 := by
    intro n hn
    rw [hGdef, Polynomial.finsetSum_coeff, Finset.sum_eq_zero]
    intro b hb
    have hbk : b < k + 1 := Finset.mem_range.mp hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by omega), mul_zero]
  have G_natDegree : G.natDegree = k := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      exact fun n hn => G_coeff_gt n hn
    · rw [G_coeff_le k le_rfl]
      intro hzero
      have h0 := congrFun hzero 0
      simp only [Pi.zero_apply] at h0
      have h1 : (fac 0).coeff k = 1 := by
        rw [← fac_deg 0]; exact (fac_monic 0).coeff_natDegree
      rw [h1] at h0
      exact one_ne_zero h0
  have G_monic : G.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, G_natDegree, G_coeff_le k le_rfl]
    funext z
    show (fac z).coeff k = 1
    rw [← fac_deg z]
    exact (fac_monic z).coeff_natDegree
  have G_hol : HolCoeffs G 0 := by
    intro n
    rcases le_or_gt n k with hn | hn
    · rw [G_coeff_le n hn]
      have hev : Gan.coeff n =ᶠ[𝓝 (0 : ℂ)] (fun z => (fac z).coeff n) := by
        filter_upwards [hV0mem] with z hz
        have hz' : fac z = Pz Gan z := by
          rw [fac_eq z, if_pos hz]
        rw [hz']
        exact (Polynomial.coeff_map (evAt z) n).symm
      exact (hGanhol n).congr hev
    · rw [G_coeff_gt n hn]; exact analyticAt_const
  have PzG_fib : ∀ z, Pz G z = fac z := by
    intro z
    ext n
    rcases le_or_gt n k with hn | hn
    · rw [Pz, Polynomial.coeff_map, G_coeff_le n hn]
      rfl
    · rw [Pz, Polynomial.coeff_map, G_coeff_gt n hn, evAt_apply, Pi.zero_apply]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [fac_deg z]; exact hn)).symm
  have hPzG0 : Pz G 0 = (X - C α) ^ k := by
    rw [PzG_fib 0, fac_eq 0, if_pos h0V0]
    exact hGan0
  -- the remainder of the division by `G` vanishes
  have hmod : P %ₘ G = 0 := by
    ext n z
    simp only [Polynomial.coeff_zero, Pi.zero_apply]
    have h1 : (P %ₘ G).coeff n z = ((P %ₘ G).map (evAt z)).coeff n :=
      (Polynomial.coeff_map (evAt z) n).symm
    rw [h1, Polynomial.map_modByMonic (evAt z) G_monic]
    change ((Pz P z) %ₘ (Pz G z)).coeff n = 0
    rw [show Pz G z = fac z from PzG_fib z]
    rw [show Pz P z %ₘ fac z = 0 from
      (Polynomial.modByMonic_eq_zero_iff_dvd (fac_monic z)).mpr (fac_dvd z)]
    simp
  have hPG : P = G * (P /ₘ G) := by
    have h := Polynomial.modByMonic_add_div P G
    rw [hmod, zero_add] at h
    exact h.symm
  exact ⟨G, G_monic, G_natDegree, G_hol, hPzG0, P /ₘ G,
    Polynomial.Monic.of_mul_monic_left G_monic (hPG ▸ hmon), hPG⟩

end Work.WilC4aP
