import Mathlib
import Submission.Work.EKLComp.volume_preimage_box_absdet_one
import Submission.Work.EKLComp.exists_euclid_orthonormal_normal_frame
import Submission.Work.EKLComp.frame_matrix_absdet_one
import Submission.Work.EKLComp.det_ne_zero_of_independent_cols
import Submission.Work.EKLComp.dot_expansion_orthonormal
import Submission.Work.EKLComp.mem_span_pair_of_orthogonal_vector

namespace Work.EKLComp

set_option maxHeartbeats 2000000

open MeasureTheory Matrix
open scoped BigOperators ENNReal

abbrev E3 := Fin 3 → ℝ

noncomputable def matLinEquiv (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) : E3 ≃ₗ[ℝ] E3 :=
  Matrix.SpecialLinearGroup.toLin' (⟨g, h⟩ : Matrix.SpecialLinearGroup (Fin 3) ℝ)

noncomputable def matBasis (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) : Module.Basis (Fin 3) ℝ E3 :=
  (Pi.basisFun ℝ (Fin 3)).map (matLinEquiv g h)

noncomputable def matLattice (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) : AddSubgroup E3 :=
  (Submodule.span ℤ (Set.range (matBasis g h))).toAddSubgroup

lemma matLinEquiv_apply (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) (v : E3) :
    matLinEquiv g h v = g *ᵥ v := by
  change (Matrix.toLin' g) v = g *ᵥ v
  rw [Matrix.toLin'_apply]

lemma matLinEquiv_det (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) :
    LinearMap.det (matLinEquiv g h).toLinearMap = 1 := by
  have hL : (matLinEquiv g h).toLinearMap = Matrix.toLin' g := by
    refine LinearMap.ext (fun v => ?_)
    show matLinEquiv g h v = (Matrix.toLin' g) v
    rw [matLinEquiv_apply, Matrix.toLin'_apply]
  rw [hL, LinearMap.det_toLin', h]

lemma matBasis_apply (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) (i : Fin 3) :
    matBasis g h i = g.col i := by
  rw [matBasis, Module.Basis.map_apply, matLinEquiv_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]

lemma sum_smul_basis (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) (c : Fin 3 → ℤ) :
    (∑ i, c i • (matBasis g h) i) = g *ᵥ (fun j => (c j : ℝ)) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, matBasis_apply, Matrix.col_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

instance instCountableBasisLattice (b : Module.Basis (Fin 3) ℝ E3) :
    Countable ↥((Submodule.span ℤ (Set.range b)).toAddSubgroup) := by
  show Countable ↥(Submodule.span ℤ (Set.range b))
  infer_instance

lemma mem_matLattice_iff (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) (x : E3) :
    x ∈ matLattice g h ↔ ∃ c : Fin 3 → ℤ, x = g *ᵥ (fun j => (c j : ℝ)) := by
  change x ∈ Submodule.span ℤ (Set.range (matBasis g h)) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, sum_smul_basis]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [sum_smul_basis]⟩

lemma volume_fundStd : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = (1 : ℝ≥0∞) := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]; simp

lemma volume_matBasis_fund (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1) :
    volume (ZSpan.fundamentalDomain (matBasis g h)) = (1 : ℝ≥0∞) := by
  have hb : matBasis g h = (Pi.basisFun ℝ (Fin 3)).map (matLinEquiv g h) := rfl
  rw [hb, ← ZSpan.map_fundamentalDomain (Pi.basisFun ℝ (Fin 3)) (matLinEquiv g h)]
  have hcoe : (⇑(matLinEquiv g h) : E3 → E3) = ⇑((matLinEquiv g h).toLinearMap) :=
    LinearEquiv.coe_toLinearMap _
  rw [hcoe, Measure.addHaar_image_linearMap volume (matLinEquiv g h).toLinearMap]
  rw [matLinEquiv_det, volume_fundStd]
  simp

lemma minkowski (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1)
    {s : Set E3} (hsymm : ∀ x ∈ s, -x ∈ s) (hconv : Convex ℝ s)
    (hvol : (8 : ℝ≥0∞) < volume s) :
    ∃ x : E3, x ≠ 0 ∧ x ∈ matLattice g h ∧ x ∈ s := by
  have fund := ZSpan.isAddFundamentalDomain' (matBasis g h) volume
  have hmain : volume (ZSpan.fundamentalDomain (matBasis g h)) * 2 ^ Module.finrank ℝ E3
      < volume s := by
    rw [volume_matBasis_fund g h, Module.finrank_fin_fun]
    norm_num
    exact hvol
  obtain ⟨x, hx0, hxs⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hsymm hconv hmain
  exact ⟨(x : E3), fun hx => hx0 (Subtype.ext hx), x.2, hxs⟩

lemma norm_ge_of_mem_matLattice (ρ : ℝ) (g : Matrix (Fin 3) (Fin 3) ℝ) (h : g.det = 1)
    (hmin : ∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖g *ᵥ (fun j => (m j : ℝ))‖)
    (x : E3) (hx : x ∈ matLattice g h) (hx0 : x ≠ 0) : ρ ≤ ‖x‖ := by
  obtain ⟨c, rfl⟩ := (mem_matLattice_iff g h x).1 hx
  exact hmin c (fun hc => hx0 (by rw [hc]; funext j; simp [Matrix.mulVec]))

-- boxes
def box__thick_lattice_short_basis (a : Fin 3 → ℝ) : Set E3 := Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i))

lemma mem_box {a : Fin 3 → ℝ} (ha : ∀ i, 0 ≤ a i) (x : E3) :
    x ∈ box__thick_lattice_short_basis a ↔ ∀ i, |x i| ≤ a i := by
  rw [box__thick_lattice_short_basis, Set.mem_pi]
  simp only [Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    have hi := h i
    rw [Set.mem_Icc] at hi
    rw [abs_le]
    exact ⟨hi.1, hi.2⟩
  · intro h i
    rw [Set.mem_Icc]
    exact abs_le.mp (h i)

lemma convex_box (a : Fin 3 → ℝ) : Convex ℝ (box__thick_lattice_short_basis a) := by
  rw [box__thick_lattice_short_basis]
  exact convex_pi (fun i _ => convex_Icc _ _)

lemma neg_mem_box (a : Fin 3 → ℝ) (x : E3) (hx : x ∈ box__thick_lattice_short_basis a) : -x ∈ box__thick_lattice_short_basis a := by
  rw [box__thick_lattice_short_basis, Set.mem_pi] at hx ⊢
  intro i hi
  have h := hx i hi
  rw [Set.mem_Icc] at h ⊢
  simp only [Pi.neg_apply]
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

lemma vol_box (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    volume (box__thick_lattice_short_basis a) = ENNReal.ofReal (∏ i, (2 * a i)) := by
  have h1 : box__thick_lattice_short_basis a = Set.Icc (fun i => -(a i)) a := by rw [box__thick_lattice_short_basis, Set.pi_univ_Icc]
  rw [h1, Real.volume_Icc_pi]
  rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun i => 2 * a i) (fun i _ => by linarith [ha i])]
  apply Finset.prod_congr rfl
  intro i _
  rw [show a i - -(a i) = 2 * a i by ring]

lemma convex_preimage_box (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    Convex ℝ ((Matrix.toLin' M) ⁻¹' box__thick_lattice_short_basis a) :=
  (convex_box a).linear_preimage _

lemma neg_mem_preimage_box (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ)
    (x : E3) (hx : x ∈ (Matrix.toLin' M) ⁻¹' box__thick_lattice_short_basis a) : -x ∈ (Matrix.toLin' M) ⁻¹' box__thick_lattice_short_basis a := by
  rw [Set.mem_preimage] at hx ⊢
  rw [box__thick_lattice_short_basis, Set.mem_pi] at hx ⊢
  intro i hi
  have hi' := hx i hi
  rw [Set.mem_Icc] at hi' ⊢
  have hneg : ((Matrix.toLin' M) (-x)) i = -(((Matrix.toLin' M) x) i) := by
    rw [map_neg, Pi.neg_apply]
  rw [hneg]
  exact ⟨by linarith [hi'.2], by linarith [hi'.1]⟩

lemma vol_preimage_box (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : |M.det| = 1) (a : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    volume ((Matrix.toLin' M) ⁻¹' box__thick_lattice_short_basis a) = ENNReal.ofReal (∏ i, (2 * a i)) := by
  have hb : box__thick_lattice_short_basis a = Set.pi Set.univ (fun i => Set.Icc (-(a i)) (a i)) := rfl
  rw [hb, volume_preimage_box_absdet_one M hM a]
  rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun i => 2 * a i) (fun i _ => by linarith [ha i])]

lemma norm_le_of_coord (x : E3) (c : ℝ) (hc : 0 ≤ c) (h : ∀ i, |x i| ≤ c) : ‖x‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 (fun i => by rw [Real.norm_eq_abs]; exact h i)

lemma eight_lt_ofReal {x : ℝ} (hx : 8 < x) : (8 : ℝ≥0∞) < ENNReal.ofReal x := by
  have h8 : (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) := (ENNReal.ofReal_ofNat 8).symm
  rw [h8, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  exact hx

lemma linearIndependent_three (x1 x2 x3 : E3)
    (h12 : LinearIndependent ℝ ![x1, x2])
    (h3 : x3 ∉ Submodule.span ℝ ({x1, x2} : Set E3)) :
    LinearIndependent ℝ ![x1, x2, x3] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • x1 + c 1 • x2 + c 2 • x3 = 0 := by
    have h := hc; rw [Fin.sum_univ_three] at h; simpa using h
  by_cases h2 : c 2 = 0
  · have hsum : c 0 • x1 + c 1 • x2 = 0 := by
      rw [h2, zero_smul, add_zero] at hc'; exact hc'
    have hc12 : ∑ i : Fin 2, (![c 0, c 1] : Fin 2 → ℝ) i • (![x1, x2] : Fin 2 → E3) i = 0 := by
      rw [Fin.sum_univ_two]; simpa using hsum
    have hz := (Fintype.linearIndependent_iff.mp h12) ![c 0, c 1] hc12
    have hc0 : c 0 = 0 := hz 0
    have hc1 : c 1 = 0 := hz 1
    intro i; fin_cases i <;> assumption
  · exfalso
    apply h3
    rw [Submodule.mem_span_pair]
    refine ⟨-((c 2)⁻¹ * c 0), -((c 2)⁻¹ * c 1), ?_⟩
    have h3' : c 2 • x3 = -(c 0 • x1 + c 1 • x2) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc'
    have key : -((c 2)⁻¹ * c 0) • x1 + -((c 2)⁻¹ * c 1) • x2 = x3 := by
      have h4 := congr_arg (fun z => (c 2)⁻¹ • z) h3'
      rw [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_neg, smul_add, smul_smul, smul_smul] at h4
      rw [h4]; module
    exact key

theorem thick_lattice_short_basis (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Matrix (Fin 3) (Fin 3) ℝ, g.det = 1 →
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec g (fun j => (m j : ℝ))‖) →
      ∃ M : Matrix (Fin 3) (Fin 3) ℤ, M.det ≠ 0 ∧
        ∀ j : Fin 3, ‖Matrix.mulVec g (fun k => ((M k j : ℤ) : ℝ))‖ ≤ C := by
  refine ⟨8 / ρ ^ 2 + 4 / Real.sqrt ρ + 4, ?_, ?_⟩
  · have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
    positivity
  · intro g hdet hmin
    have hdetabs : |g.det| = 1 := by rw [hdet]; norm_num
    have Hge : ∀ x : E3, x ∈ matLattice g hdet → x ≠ 0 → ρ ≤ ‖x‖ :=
      fun x hx hx0 => norm_ge_of_mem_matLattice ρ g hdet hmin x hx hx0
    have hC2 : (2 : ℝ) ≤ 8 / ρ ^ 2 + 4 / Real.sqrt ρ + 4 := by
      have h1 : 0 ≤ 8 / ρ ^ 2 + 4 / Real.sqrt ρ := by positivity
      linarith
    have hC2sq : (1 + 2 / Real.sqrt ρ) ≤ 8 / ρ ^ 2 + 4 / Real.sqrt ρ + 4 := by
      have h1 : 0 ≤ 8 / ρ ^ 2 := by positivity
      have h2 : (2 : ℝ) / Real.sqrt ρ ≤ 4 / Real.sqrt ρ :=
        div_le_div_of_nonneg_right (by norm_num) (le_of_lt (Real.sqrt_pos.2 hρ))
      linarith
    have hvol1 : (8 : ℝ≥0∞) < volume (box__thick_lattice_short_basis (fun _ : Fin 3 => (2 : ℝ))) := by
      rw [vol_box _ (fun _ => by norm_num)]
      rw [show (∏ i : Fin 3, (2 * (2 : ℝ))) = 64 by rw [Fin.prod_univ_three]; norm_num]
      exact eight_lt_ofReal (by norm_num)
    obtain ⟨x1, hx1ne, hx1L, hx1box⟩ := minkowski g hdet (neg_mem_box _) (convex_box _) hvol1
    have hx1coord : ∀ i, |x1 i| ≤ 2 := (mem_box (fun _ => by norm_num) x1).1 hx1box
    have hx1norm : ‖x1‖ ≤ 2 := norm_le_of_coord x1 2 (by norm_num) hx1coord
    have hx1ge : ρ ≤ ‖x1‖ := Hge x1 hx1L hx1ne
    have hρle2 : ρ ≤ 2 := le_trans hx1ge hx1norm
    obtain ⟨k, -, hkmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Fin 3)) (fun i => |x1 i|) Finset.univ_nonempty
    have hx1k : |x1 k| = ‖x1‖ := by
      apply le_antisymm
      · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x1 k
      · exact norm_le_of_coord x1 |x1 k| (abs_nonneg _) (fun i => hkmax i (Finset.mem_univ i))
    set L : ℝ := 2 / Real.sqrt ρ with hL
    set a2 : Fin 3 → ℝ := fun i => if i = k then ρ / 2 else L with ha2
    have ha2nn : ∀ i, 0 ≤ a2 i := by
      intro i
      simp only [ha2]
      by_cases h : i = k
      · rw [if_pos h]; linarith [hρ]
      · rw [if_neg h, hL]; positivity
    have hLsq : (2 * L) * (2 * L) = 16 / ρ := by
      rw [hL]; field_simp; rw [Real.sq_sqrt hρ.le]; ring
    have hprod2 : (∏ i : Fin 3, (2 * a2 i)) = 16 := by
      have hk : (2 * a2 k) = ρ := by simp [ha2]; ring
      have herase : (∏ i ∈ (Finset.univ : Finset (Fin 3)).erase k, (2 * a2 i))
          = (2 * L) * (2 * L) := by
        rw [Finset.prod_congr rfl (fun i hi => by
          have hik : i ≠ k := Finset.ne_of_mem_erase hi
          simp only [ha2]; rw [if_neg hik])]
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
          Fintype.card_fin]
        ring
      rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin 3)) (fun i => 2 * a2 i)
            (Finset.mem_univ k), hk, herase, hLsq]
      field_simp
    have hvol2 : (8 : ℝ≥0∞) < volume (box__thick_lattice_short_basis a2) := by
      rw [vol_box a2 ha2nn, hprod2]
      exact eight_lt_ofReal (by norm_num)
    obtain ⟨x2, hx2ne, hx2L, hx2box⟩ := minkowski g hdet (neg_mem_box a2) (convex_box a2) hvol2
    have hx2coord : ∀ i, |x2 i| ≤ a2 i := (mem_box ha2nn x2).1 hx2box
    have hx2k : |x2 k| ≤ ρ / 2 := by
      have h := hx2coord k
      simp only [ha2] at h
      simpa using h
    have hx2norm : ‖x2‖ ≤ 1 + L := by
      have hLnn : 0 ≤ L := by rw [hL]; positivity
      apply norm_le_of_coord x2 (1 + L) (by linarith)
      intro i
      have h := hx2coord i
      simp only [ha2] at h
      by_cases hk : i = k
      · rw [if_pos hk] at h
        linarith [h, hρle2, hLnn]
      · rw [if_neg hk] at h
        linarith [h, hLnn]
    have hnotc : ∀ c : ℝ, x2 ≠ c • x1 := by
      intro c hc
      have hcne : c ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc; exact hx2ne hc
      have hmem : c • x1 ∈ matLattice g hdet := hc ▸ hx2L
      have hne : c • x1 ≠ 0 := by intro h0; exact hx2ne (hc ▸ h0)
      have hge : ρ ≤ ‖c • x1‖ := Hge (c • x1) hmem hne
      have heq : |x2 k| = ‖c • x1‖ := by
        have h1 : |x2 k| = |c| * |x1 k| := by rw [hc, Pi.smul_apply, smul_eq_mul, abs_mul]
        have h2 : ‖c • x1‖ = |c| * |x1 k| := by rw [norm_smul, Real.norm_eq_abs, hx1k]
        rw [h1, h2]
      rw [heq] at hx2k
      linarith [hge, hx2k, hρ]
    have hx1x2 : LinearIndependent ℝ ![x1, x2] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : c 0 • x1 + c 1 • x2 = 0 := by
        have h := hc; rw [Fin.sum_univ_two] at h; simpa using h
      by_cases h1 : c 1 = 0
      · have hx1 : c 0 • x1 = 0 := by simpa [h1] using hc'
        have hc0 : c 0 = 0 := by
          rcases smul_eq_zero.mp hx1 with h | h
          · exact h
          · exact absurd h hx1ne
        intro i; fin_cases i <;> assumption
      · have hc0 : c 0 ≠ 0 := by
          intro h0
          have : c 1 • x2 = 0 := by simpa [h0] using hc'
          rcases smul_eq_zero.mp this with h | h
          · exact absurd h h1
          · exact absurd h hx2ne
        have h2 : c 0 • x1 = -(c 1 • x2) := by rw [eq_neg_iff_add_eq_zero]; exact hc'
        have hx1eq : x1 = (-(c 1 / c 0)) • x2 := by
          calc x1 = (c 0)⁻¹ • (c 0 • x1) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
            _ = (c 0)⁻¹ • (-(c 1 • x2)) := by rw [h2]
            _ = (-(c 1 / c 0)) • x2 := by
                  rw [smul_neg, smul_smul, ← neg_smul,
                    show -((c 0)⁻¹ * c 1) = -(c 1 / c 0) by ring]
        have he : (-(c 1 / c 0)) ≠ 0 := by
          intro hh
          exact div_ne_zero h1 hc0 (neg_eq_zero.mp hh)
        have hx2eq : x2 = (-(c 1 / c 0))⁻¹ • x1 := by
          rw [hx1eq, smul_smul, inv_mul_cancel₀ he, one_smul]
        exact absurd (hnotc ((-(c 1 / c 0))⁻¹) hx2eq) not_false
    obtain ⟨e1, e2, u, he1, he2, heu, he12, he1u, he2u, hu1, hu2⟩ :=
      exists_euclid_orthonormal_normal_frame x1 x2 hx1x2
    set Mf : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![e1, e2, u] with hMf
    have hMfdet : |Mf.det| = 1 := by
      rw [hMf]; exact frame_matrix_absdet_one e1 e2 u he1 he2 heu he12 he1u he2u
    set η : ℝ := 8 / ρ ^ 2 with hη
    have hηpos : 0 < η := by rw [hη]; positivity
    set a3 : Fin 3 → ℝ := ![ρ / 2, ρ / 2, η] with ha3
    have ha3nn : ∀ i, 0 ≤ a3 i := by
      intro i; fin_cases i <;> simp [ha3, hη] <;> positivity
    have hprod3 : (∏ i : Fin 3, (2 * a3 i)) = 16 := by
      have h0 : a3 0 = ρ / 2 := by simp [ha3]
      have h1 : a3 1 = ρ / 2 := by simp [ha3]
      have h2 : a3 2 = η := by simp [ha3]
      rw [Fin.prod_univ_three, h0, h1, h2, hη]
      field_simp
      ring
    have hvol3 : (8 : ℝ≥0∞) < volume ((Matrix.toLin' Mf) ⁻¹' box__thick_lattice_short_basis a3) := by
      rw [vol_preimage_box Mf hMfdet a3 ha3nn, hprod3]
      exact eight_lt_ofReal (by norm_num)
    have hrow0 : ∀ x : E3, ((Matrix.toLin' Mf) x) 0 = ∑ i, e1 i * x i := by
      intro x
      simp only [Matrix.toLin'_apply, hMf, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Equiv.refl_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
    have hrow1 : ∀ x : E3, ((Matrix.toLin' Mf) x) 1 = ∑ i, e2 i * x i := by
      intro x
      simp only [Matrix.toLin'_apply, hMf, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Equiv.refl_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
    have hrow2 : ∀ x : E3, ((Matrix.toLin' Mf) x) 2 = ∑ i, u i * x i := by
      intro x
      simp only [Matrix.toLin'_apply, hMf, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Equiv.refl_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
    have hx0_exists : ∃ x0 : E3, x0 ∈ matLattice g hdet ∧
        (∑ i, u i * x0 i) ≠ 0 ∧ |∑ i, u i * x0 i| ≤ η := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨x3, hx3ne, hx3L, hx3box⟩ :=
        minkowski g hdet (neg_mem_preimage_box Mf a3) (convex_preimage_box Mf a3) hvol3
      have hx3coord : ∀ i, |((Matrix.toLin' Mf) x3) i| ≤ a3 i :=
        (mem_box ha3nn ((Matrix.toLin' Mf) x3)).1 hx3box
      have hphi : (∑ i, u i * x3 i) = 0 := by
        by_contra hne'
        have h1 := hcon x3 hx3L hne'
        have h2 : |∑ i, u i * x3 i| ≤ η := by
          have h := hx3coord 2
          rw [hrow2 x3] at h
          rwa [ha3] at h
        linarith
      have hpar := dot_expansion_orthonormal e1 e2 u x3 he1 he2 heu he12 he1u he2u
      have hcoords0 : (∑ i, e1 i * x3 i) ^ 2 ≤ (ρ / 2) ^ 2 := by
        have h := hx3coord 0
        rw [hrow0 x3, ha3] at h
        simp only [Matrix.cons_val_zero] at h
        rw [abs_le] at h
        nlinarith [h.1, h.2, hρ]
      have hcoords1 : (∑ i, e2 i * x3 i) ^ 2 ≤ (ρ / 2) ^ 2 := by
        have h := hx3coord 1
        rw [hrow1 x3, ha3] at h
        simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
        rw [abs_le] at h
        nlinarith [h.1, h.2, hρ]
      have hsum : (∑ i, x3 i * x3 i) ≤ ρ ^ 2 / 2 := by
        rw [hpar, hphi]
        nlinarith [hcoords0, hcoords1]
      have hsum_lt : (∑ i, x3 i * x3 i) < ρ ^ 2 := by nlinarith [hsum, hρ]
      have hsqrt_lt : Real.sqrt (∑ i, x3 i * x3 i) < ρ := by
        rw [Real.sqrt_lt' hρ]; exact hsum_lt
      have hle : ‖x3‖ ≤ Real.sqrt (∑ i, x3 i * x3 i) := by
        apply norm_le_of_coord x3 _ (Real.sqrt_nonneg _)
        intro i
        apply Real.abs_le_sqrt
        rw [sq]
        exact Finset.single_le_sum (f := fun j => x3 j * x3 j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
      have : ‖x3‖ < ρ := lt_of_le_of_lt hle hsqrt_lt
      exact absurd (Hge x3 hx3L hx3ne) (not_le.mpr this)
    obtain ⟨x0, hx0L, hx0ne, hx0le⟩ := hx0_exists
    set c0 : ℝ := ∑ i, u i * x0 i with hc0
    set p : E3 := x0 - c0 • u with hp
    have hup : ∑ i, u i * p i = 0 := by
      have hexp : ∀ i : Fin 3, u i * p i = u i * x0 i - c0 * (u i * u i) := by
        intro i; rw [hp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (∑ i : Fin 3, u i * x0 i) = c0 from hc0.symm, heu, mul_one, sub_self]
    have hpmem : p ∈ Submodule.span ℝ ({x1, x2} : Set E3) :=
      mem_span_pair_of_orthogonal_vector x1 x2 u p hu1 hu2 heu hup hx1x2
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hpmem
    set γ : E3 := (round s : ℝ) • x1 + (round t : ℝ) • x2 with hγ
    have hγL : γ ∈ matLattice g hdet := by
      rw [hγ]
      apply AddSubgroup.add_mem
      · rw [Int.cast_smul_eq_zsmul ℝ (round s) x1]
        exact AddSubgroup.zsmul_mem _ hx1L _
      · rw [Int.cast_smul_eq_zsmul ℝ (round t) x2]
        exact AddSubgroup.zsmul_mem _ hx2L _
    set x3 : E3 := x0 - γ with hx3def
    have hx3L : x3 ∈ matLattice g hdet := hx3def ▸ AddSubgroup.sub_mem _ hx0L hγL
    have hx3phi : ∑ i, u i * x3 i = c0 := by
      have hexp : ∀ i : Fin 3, u i * x3 i = u i * x0 i - u i * γ i := by
        intro i; rw [hx3def, Pi.sub_apply]; ring
      rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib]
      have hγ0 : ∑ i, u i * γ i = 0 := by
        have hexpγ : ∀ i : Fin 3, u i * γ i
            = (round s : ℝ) * (u i * x1 i) + (round t : ℝ) * (u i * x2 i) := by
          intro i; rw [hγ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hexpγ i), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hu1, hu2, mul_zero, mul_zero, add_zero]
      rw [hγ0, sub_zero, show (∑ i : Fin 3, u i * x0 i) = c0 from hc0.symm]
    have hx3ne : x3 ≠ 0 := by
      intro h0
      have : (∑ i, u i * x3 i) = 0 := by rw [h0]; simp
      rw [hx3phi] at this
      exact hx0ne this
    have hx3notspan : x3 ∉ Submodule.span ℝ ({x1, x2} : Set E3) := by
      intro hmem
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
      have hzero : ∑ i, u i * x3 i = 0 := by
        rw [← hab]
        have hexp : ∀ i : Fin 3, u i * (a • x1 + b • x2) i
            = a * (u i * x1 i) + b * (u i * x2 i) := by
          intro i; rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring
        rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hu1, hu2, mul_zero, mul_zero, add_zero]
      rw [hx3phi] at hzero
      exact hx0ne hzero
    have hind3 : LinearIndependent ℝ ![x1, x2, x3] :=
      linearIndependent_three x1 x2 x3 hx1x2 hx3notspan
    have hx3bound : ‖x3‖ ≤ η + 4 / Real.sqrt ρ + 4 := by
      have hu_le : ‖u‖ ≤ 1 := by
        apply norm_le_of_coord u 1 (by norm_num)
        intro i
        have h2 : (u i) ^ 2 ≤ 1 := by
          rw [← heu, sq]
          exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg _)
            (Finset.mem_univ i)
        rw [abs_le]; exact ⟨by nlinarith [h2], by nlinarith [h2]⟩
      have hpg : p - γ = (s - (round s : ℝ)) • x1 + (t - (round t : ℝ)) • x2 := by
        rw [← hst, hγ]
        simp only [sub_smul]
        abel
      have hpg_bound : ‖p - γ‖ ≤ 1 + (1 + L) / 2 := by
        have h1 : |s - (round s : ℝ)| ≤ 1 / 2 := abs_sub_round s
        have h2 : |t - (round t : ℝ)| ≤ 1 / 2 := abs_sub_round t
        calc ‖p - γ‖ = ‖(s - (round s : ℝ)) • x1 + (t - (round t : ℝ)) • x2‖ := by rw [hpg]
          _ ≤ ‖(s - (round s : ℝ)) • x1‖ + ‖(t - (round t : ℝ)) • x2‖ := norm_add_le _ _
          _ = |s - (round s : ℝ)| * ‖x1‖ + |t - (round t : ℝ)| * ‖x2‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ (1 / 2) * 2 + (1 / 2) * (1 + L) := by
                apply add_le_add
                · exact mul_le_mul h1 hx1norm (norm_nonneg _) (by norm_num)
                · exact mul_le_mul h2 hx2norm (norm_nonneg _) (by norm_num)
          _ = 1 + (1 + L) / 2 := by ring
      have hfinal : (1 + (1 + L) / 2) + η * 1 ≤ η + 4 / Real.sqrt ρ + 4 := by
        rw [hL, hη, mul_one]
        have hX : 0 ≤ 1 / Real.sqrt ρ := by positivity
        have he : (1 + 2 / Real.sqrt ρ) / 2 = 1 / 2 + 1 / Real.sqrt ρ := by ring
        rw [he]
        have he2 : 8 / ρ ^ 2 + 4 / Real.sqrt ρ + 4
            - (1 + (1 / 2 + 1 / Real.sqrt ρ) + 8 / ρ ^ 2)
            = 3 * (1 / Real.sqrt ρ) + 5 / 2 := by ring
        linarith [hX, he2]
      have hdec : x3 = (p - γ) + c0 • u := by
        rw [hx3def, hp, hγ]; abel
      calc ‖x3‖ = ‖(p - γ) + c0 • u‖ := by rw [hdec]
        _ ≤ ‖p - γ‖ + ‖c0 • u‖ := norm_add_le _ _
        _ = ‖p - γ‖ + |c0| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (1 + (1 + L) / 2) + η * 1 := by
              have h1 : |c0| ≤ η := by rw [hc0]; exact hx0le
              have h2 : 0 ≤ ‖p - γ‖ := norm_nonneg _
              have h3 : 0 ≤ η := le_of_lt hηpos
              nlinarith [hpg_bound, h1, hu_le, norm_nonneg u, abs_nonneg c0]
        _ ≤ η + 4 / Real.sqrt ρ + 4 := hfinal
    obtain ⟨m1, hm1⟩ := (mem_matLattice_iff g hdet x1).1 hx1L
    obtain ⟨m2, hm2⟩ := (mem_matLattice_iff g hdet x2).1 hx2L
    obtain ⟨m3, hm3⟩ := (mem_matLattice_iff g hdet x3).1 hx3L
    have h0c : ‖g *ᵥ (fun k => (m1 k : ℝ))‖ ≤ η + 4 / Real.sqrt ρ + 4 := by
      rw [← hm1]; exact le_trans hx1norm hC2
    have h1c : ‖g *ᵥ (fun k => (m2 k : ℝ))‖ ≤ η + 4 / Real.sqrt ρ + 4 := by
      rw [← hm2]; exact le_trans hx2norm hC2sq
    have h2c : ‖g *ᵥ (fun k => (m3 k : ℝ))‖ ≤ η + 4 / Real.sqrt ρ + 4 := by
      rw [← hm3]; exact hx3bound
    refine ⟨fun i j => (![m1, m2, m3] j) i, ?_, ?_⟩
    · apply det_ne_zero_of_independent_cols
      have hcol : (fun j => (fun i => (((fun i j => (![m1, m2, m3] j) i) i j : ℤ) : ℝ)))
          = (![fun i => (m1 i : ℝ), fun i => (m2 i : ℝ), fun i => (m3 i : ℝ)] : Fin 3 → E3) := by
        funext j i; fin_cases j <;> rfl
      rw [hcol]
      have hker : (matLinEquiv g hdet).symm.toLinearMap.ker = ⊥ :=
        LinearMap.ker_eq_bot.mpr (matLinEquiv g hdet).symm.injective
      have hmap := hind3.map' (matLinEquiv g hdet).symm.toLinearMap hker
      have hcomp : ((matLinEquiv g hdet).symm.toLinearMap ∘ ![x1, x2, x3])
          = (![fun i => (m1 i : ℝ), fun i => (m2 i : ℝ), fun i => (m3 i : ℝ)] : Fin 3 → E3) := by
        funext j
        fin_cases j
        · show (matLinEquiv g hdet).symm x1 = _
          refine ((matLinEquiv g hdet).symm_apply_eq).mpr ?_
          show x1 = matLinEquiv g hdet (fun i => (m1 i : ℝ))
          rw [matLinEquiv_apply]; exact hm1
        · show (matLinEquiv g hdet).symm x2 = _
          refine ((matLinEquiv g hdet).symm_apply_eq).mpr ?_
          show x2 = matLinEquiv g hdet (fun i => (m2 i : ℝ))
          rw [matLinEquiv_apply]; exact hm2
        · show (matLinEquiv g hdet).symm x3 = _
          refine ((matLinEquiv g hdet).symm_apply_eq).mpr ?_
          show x3 = matLinEquiv g hdet (fun i => (m3 i : ℝ))
          rw [matLinEquiv_apply]; exact hm3
      rw [← hcomp]; exact hmap
    · intro j
      fin_cases j
      · simpa using h0c
      · simpa using h1c
      · simpa using h2c

end Work.EKLComp
