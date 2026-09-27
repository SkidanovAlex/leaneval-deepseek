import Mathlib
import Submission.Work.Mostow.cuspHoro.cuspThinDefs
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.horSpec

/-!
# The Margulis thin region of a cusp: separation, invariance, fibre structure

The part of the cusp theory for a lattice `Γ ≤ PO(n,1)` and a parabolic fixed point `ξ` that uses
only the Margulis lemma in the form `Work.Mostow.margulisCusp` (proved, sorry-free).  The thin
region is `cuspThin Γ ξ ε = {u | ∃ q ∈ Γ parabolic, bd q ξ = ξ, hdist u (q • u) < ε}`.

* `cuspThin_separation` (all `n ≥ 2`): thin regions of distinct parabolic fixed points are
  disjoint below the Margulis threshold;
* `cuspThin_precise_separation`: consequently the thin region at `ξ` is precisely invariant:
  an element of `Γ` not fixing `ξ` moves it to a disjoint set;
* `cosh_hdist_of_level_preserving`, `flatAffine`: the flat (horospherical) action of a level
  preserving element fixing `ξ` is affine and isometric on `ξ^⊥`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Work.Mostow.cuspHoro

noncomputable section

variable {n : ℕ}

/-- The hyperbolic cosine of the displacement of a level preserving element fixing `ξ`, in terms
of the flat displacement. -/
theorem cosh_hdist_of_level_preserving (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hlev : ∀ u : E n, lev ξ (g • u) = lev ξ u) (u : E n) :
    Real.cosh (hdist u (g • u)) = 1 + (lev ξ u) ^ 2 * ‖yc ξ (g • u) - yc ξ u‖ ^ 2 / 2 := by
  have h := levYcFormula hξ u (g • u)
  rw [hlev u] at h
  have hL : lev ξ u ≠ 0 := ne_of_gt (lev_pos ξ hξ u)
  rw [div_self hL, Real.log_one, Real.cosh_zero] at h
  rw [norm_sub_rev (yc ξ u) (yc ξ (g • u))] at h
  rw [h]; ring

/-- A level preserving element fixing `ξ` acts on the flat space by an affine isometry. -/
theorem flatAffine (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) (hβ : busemann ξ (g • (0 : E n)) = 0) :
    ∃ (A : E n →ₗ[ℝ] E n) (v : E n), inner ℝ v ξ = 0 ∧
      (∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) ∧
      (∀ u : E n, lev ξ (g • u) = lev ξ u) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ∀ D : ℝ, 0 < D →
        yc ξ (g • hptOf ξ y D) = A y + v) := by
  obtain ⟨A, v, hv, horth, hnorm, hpt⟩ := stabFlatAction n hA hI ξ hξ g hg hβ
  refine ⟨A, v, hv, horth, hnorm, ?_, fun y hy D hD => (hpt y D hy hD).2⟩
  intro u
  have hu : hptOf ξ (yc ξ u) (lev ξ u) = u :=
    hptOf_yc ξ hξ (lev ξ u) (lev_pos ξ hξ u) u rfl
  have hy : inner ℝ (yc ξ u) ξ = 0 := yc_inner_orth hξ
  have hlevu : 0 < lev ξ u := lev_pos ξ hξ u
  have h1 : lev ξ (g • hptOf ξ (yc ξ u) (lev ξ u)) = lev ξ u :=
    (hpt (yc ξ u) (lev ξ u) hy hlevu).1
  have h2 : lev ξ (hptOf ξ (yc ξ u) (lev ξ u)) = lev ξ u :=
    (hptOf_level ξ hξ (lev ξ u) hlevu (yc ξ u) hy).1
  rw [← hu, h1, h2]

/-- **The cusp thin regions of distinct parabolic fixed points are disjoint** (`n ≥ 2`). -/
theorem cuspThin_separation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ η : E n, ξ ∈ parFixed Γ → η ∈ parFixed Γ → ξ ≠ η →
      Disjoint (cuspThin Γ ξ ε) (cuspThin Γ η ε) := by
  obtain ⟨ε_M, hε_M, hmc⟩ := margulisCusp n hn hA hI 1
  refine ⟨min ε_M 1, lt_min hε_M one_pos, ?_⟩
  intro ξ η hξ hη hne
  refine Set.disjoint_left.mpr ?_
  intro u huξ huη
  obtain ⟨q, hqpar, hqfix, hqu⟩ := huξ
  obtain ⟨p, hppar, hpfix, hpu⟩ := huη
  have hξε : ξ ∈ Submission.Mostow.Sph n := hξ.1
  have hq_lt : hdist u ((q : PO n 1) • u) < ε_M :=
    lt_of_lt_of_le hqu (min_le_left _ _)
  have hp_le : hdist u ((p : PO n 1) • u) ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hpu (min_le_right _ _))
  have hpfixξ : bd (p : PO n 1) ξ = ξ :=
    hmc Γ hdisc u ξ q p hqpar hξε hqfix hq_lt hp_le
  exact hne (paraUniqueFixed (POBasic.ofProp hA) (HypIsoData.ofProp hI) hppar hξε hpfixξ hη.1
    hpfix).symm

/-- **The thin region at a parabolic fixed point is precisely invariant** modulo the stabiliser:
an element of `Γ` not fixing `ξ` moves it to a disjoint set (for the Margulis threshold). -/
theorem cuspThin_precise_separation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : E n, ξ ∈ parFixed Γ → ∀ γ : Γ,
      bd (γ : PO n 1) ξ ≠ ξ →
        Disjoint ((fun u : E n => (γ : PO n 1) • u) '' cuspThin Γ ξ ε)
          (cuspThin Γ ξ ε) := by
  obtain ⟨ε, hε, hsep⟩ := cuspThin_separation n hn hA hI Γ hdisc
  refine ⟨ε, hε, ?_⟩
  intro ξ hξ γ hγ
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  have hηS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hA'.bd_mem (γ : PO n 1)⁻¹ ξ hξS
  have hmem : bd (γ : PO n 1)⁻¹ ξ ∈ parFixed Γ := parFixed_invariant hA hI Γ γ⁻¹ hξ
  have hγinv : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
    rw [← hA'.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hA'.bd_one ξ hξS]
  have hne : bd (γ : PO n 1)⁻¹ ξ ≠ ξ := by
    intro h
    refine hγ ?_
    calc bd (γ : PO n 1) ξ = bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) := by rw [h]
      _ = ξ := hγinv
  refine Set.disjoint_left.mpr ?_
  rintro u ⟨v, hv, hvu⟩ hu
  obtain ⟨q, hqpar, hqfix, hqu⟩ := hu
  have hmemv : v ∈ cuspThin Γ (bd (γ : PO n 1)⁻¹ ξ) ε := by
    refine ⟨⟨(γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1),
        mul_mem (mul_mem (inv_mem γ.2) q.2) γ.2⟩, ?_, ?_, ?_⟩
    · simpa only [inv_inv] using isParabolic_conj hA hI ((γ : PO n 1)⁻¹) (q : PO n 1) hqpar
    · show bd ((γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1)) (bd (γ : PO n 1)⁻¹ ξ)
        = bd (γ : PO n 1)⁻¹ ξ
      rw [hA'.bd_mul ((γ : PO n 1)⁻¹ * (q : PO n 1)) (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hηS,
        hA'.bd_mul ((γ : PO n 1)⁻¹) (q : PO n 1) (bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ))
          (hA'.bd_mem (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hηS),
        hγinv, hqfix]
    · show hdist v (((γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1)) • v) < ε
      have h1 : ((γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1)) • v
          = (γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • v)) := by
        simp only [hA'.mul_smul]
      rw [h1]
      have h2 : hdist v ((γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • v)))
          = hdist ((γ : PO n 1) • v) ((q : PO n 1) • ((γ : PO n 1) • v)) := by
        rw [(hI'.isom_smul (γ : PO n 1) v
          ((γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • v)))).symm]
        congr 1
        rw [← hA'.mul_smul (γ : PO n 1) ((γ : PO n 1)⁻¹)
          ((q : PO n 1) • ((γ : PO n 1) • v)), mul_inv_cancel, hA'.one_smul]
      rw [h2, show (γ : PO n 1) • v = u from hvu]
      exact hqu
  have hd := hsep (bd (γ : PO n 1)⁻¹ ξ) ξ hmem hξ hne
  exact hd.le_bot ⟨hmemv, hv⟩

/-- The displacement of a flat translation at `ξ` by `v` in terms of the level. -/
theorem hdist_flat_translation (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (δ : PO n 1) (v : E n) (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) (u : E n) :
    hdist u (δ • u) = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have h := cosh_hdist_of_level_preserving hI hξ δ hlev u
  rw [hyc u] at h
  have h1 : yc ξ u + v - yc ξ u = v := by abel
  rw [h1] at h
  rw [← h, Real.arcosh_cosh (hI'.nonneg u (δ • u))]

/-- **Shimizu's lemma from a flat translation.**  If the stabiliser of the cusp `ξ` contains a
parabolic flat translation `y ↦ y + v` (`v ≠ 0`), then a small horoball at `ξ` is precisely
invariant: for `γ ∈ Γ` with `bd γ ξ ≠ ξ`, no point of the `s`-horoball at `ξ` is moved by `γ`
into that horoball. -/
theorem shimizu_of_flatTranslation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hflat : ∃ (δ : Γ) (v : E n), v ≠ 0 ∧ inner ℝ v ξ = 0 ∧ bd (δ : PO n 1) ξ = ξ ∧
      IsParabolic (δ : PO n 1) ∧
      (∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) ∧
      (∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u)) :
    ∃ s : ℝ, 0 < s ∧ ∀ γ : Γ,
      bd (γ : PO n 1) ξ ≠ ξ →
      ∀ u : E n, lev ξ u < s → s ≤ lev ξ ((γ : PO n 1) • u) := by
  obtain ⟨δ, v, hv, -, hδξ, hδpar, hyc, hlev⟩ := hflat
  have hξS : ξ ∈ Sph n := hξ.1
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hdisp : ∀ u : E n, hdist u ((δ : PO n 1) • u)
      = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) :=
    fun u => hdist_flat_translation hI hξS (δ : PO n 1) v hlev hyc u
  obtain ⟨εM, hεMpos, hmc⟩ := margulisCusp n hn hA hI 1
  set C : ℝ := min (Real.cosh εM) (Real.cosh 1) with hCdef
  have hC1 : 1 < C :=
    lt_min (Real.one_lt_cosh.mpr (ne_of_gt hεMpos)) (Real.one_lt_cosh.mpr one_ne_zero)
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have hvhalf : 0 < ‖v‖ ^ 2 / 2 := by positivity
  set s : ℝ := Real.sqrt (2 * (C - 1) / ‖v‖ ^ 2) / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    exact div_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2)) (by norm_num)
  have hs2 : s ^ 2 * ‖v‖ ^ 2 / 2 = (C - 1) / 4 := by
    rw [hsdef, div_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
    field_simp
    ring
  have hsC : 1 + s ^ 2 * ‖v‖ ^ 2 / 2 < C := by
    rw [hs2]; linarith
  have hbound : ∀ x : ℝ, 0 ≤ x → x < s →
      Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) < εM ∧
        Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) ≤ 1 := by
    intro x hx0 hx
    have hx2 : x ^ 2 < s ^ 2 := by nlinarith
    have hmul : x ^ 2 * (‖v‖ ^ 2 / 2) < s ^ 2 * (‖v‖ ^ 2 / 2) :=
      mul_lt_mul_of_pos_right hx2 hvhalf
    have hlt : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < 1 + s ^ 2 * ‖v‖ ^ 2 / 2 := by
      have h1 : x ^ 2 * ‖v‖ ^ 2 / 2 = x ^ 2 * (‖v‖ ^ 2 / 2) := by ring
      have h2 : s ^ 2 * ‖v‖ ^ 2 / 2 = s ^ 2 * (‖v‖ ^ 2 / 2) := by ring
      linarith
    have hxpos : (0:ℝ) < 1 + x ^ 2 * ‖v‖ ^ 2 / 2 := by positivity
    have hltC : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < C := lt_trans hlt hsC
    constructor
    · have hltε : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh εM :=
        lt_of_lt_of_le hltC (by rw [hCdef]; exact min_le_left _ _)
      have hmono : Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) < Real.arcosh (Real.cosh εM) :=
        (Real.arcosh_lt_arcosh hxpos (Real.cosh_pos εM)).mpr hltε
      rwa [Real.arcosh_cosh (le_of_lt hεMpos)] at hmono
    · have hlt1 : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 ≤ Real.cosh 1 :=
        le_of_lt (lt_of_lt_of_le hltC (by rw [hCdef]; exact min_le_right _ _))
      have hmono : Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) ≤ Real.arcosh (Real.cosh 1) :=
        (Real.arcosh_le_arcosh hxpos (Real.cosh_pos 1)).mpr hlt1
      rwa [Real.arcosh_cosh (le_of_lt zero_lt_one)] at hmono
  refine ⟨s, hspos, ?_⟩
  intro γ hγ u hu
  by_contra hcon
  push_neg at hcon
  have h1 : hdist u ((δ : PO n 1) • u) < εM := by
    rw [hdisp u]
    exact (hbound (lev ξ u) (le_of_lt (lev_pos ξ hξS u)) hu).1
  set σ : Γ := ⟨(γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1),
    mul_mem (mul_mem (inv_mem γ.2) δ.2) γ.2⟩ with hσdef
  have hσcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1) := rfl
  have hσmul : (γ : PO n 1) * (σ : PO n 1) = (δ : PO n 1) * (γ : PO n 1) := by
    rw [hσcoe]; group
  have h2 : hdist u ((σ : PO n 1) • u) ≤ 1 := by
    have hA1 : hdist u ((σ : PO n 1) • u)
        = hdist ((γ : PO n 1) • u) ((γ : PO n 1) • ((σ : PO n 1) • u)) :=
      (hvd.isom_smul (γ : PO n 1) u ((σ : PO n 1) • u)).symm
    have hA2 : (γ : PO n 1) • ((σ : PO n 1) • u) = (δ : PO n 1) • ((γ : PO n 1) • u) := by
      rw [← hpb.mul_smul (γ : PO n 1) (σ : PO n 1) u, hσmul, hpb.mul_smul (δ : PO n 1)
        (γ : PO n 1) u]
    rw [hA1, hA2, hdisp ((γ : PO n 1) • u)]
    exact (hbound (lev ξ ((γ : PO n 1) • u)) (le_of_lt (lev_pos ξ hξS _)) hcon).2
  have hσpar : IsParabolic (σ : PO n 1) := by
    have h := isParabolic_conj hA hI ((γ : PO n 1)⁻¹) (δ : PO n 1) hδpar
    rw [hσcoe]
    simpa only [inv_inv] using h
  have hσfix : bd (σ : PO n 1) ξ = ξ :=
    hmc Γ hΓ.1 u ξ δ σ hδpar hξS hδξ h1 h2
  have hγinvξS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hpb.bd_mem ((γ : PO n 1)⁻¹) ξ hξS
  have hbd1 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
    rw [← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hpb.bd_one ξ hξS]
  have hσfixinv : bd (σ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1)⁻¹ ξ := by
    rw [hσcoe,
      hpb.bd_mul ((γ : PO n 1)⁻¹ * (δ : PO n 1)) (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hγinvξS,
      hbd1,
      hpb.bd_mul ((γ : PO n 1)⁻¹) (δ : PO n 1) ξ hξS,
      hδξ]
  have heq : bd (γ : PO n 1)⁻¹ ξ = ξ :=
    paraUniqueFixed hpb hvd hσpar hξS hσfix hγinvξS hσfixinv
  refine hγ ?_
  have h3 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1) ξ := by rw [heq]
  rw [← h3, ← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel,
    hpb.bd_one ξ hξS]

/-- The Shimizu embedding in the Busemann (horoball) form used by the cocompactness theorem. -/
theorem horoballEmbedded_of_flatTranslation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hflat : ∃ (δ : Γ) (v : E n), v ≠ 0 ∧ inner ℝ v ξ = 0 ∧ bd (δ : PO n 1) ξ = ξ ∧
      IsParabolic (δ : PO n 1) ∧
      (∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) ∧
      (∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u)) :
    ∃ τ : ℝ, ∀ γ : Γ, bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ)
        (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ)) := by
  obtain ⟨s, hspos, hs⟩ := shimizu_of_flatTranslation n hn hA hI Γ hΓ ξ hξ hflat
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  refine ⟨Real.log s, ?_⟩
  intro γ hγ
  -- `bd γ⁻¹ ξ ≠ ξ`
  have hne : bd (γ : PO n 1)⁻¹ ξ ≠ ξ := by
    intro h
    refine hγ ?_
    have h3 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
      have h4 := hA'.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS
      rw [mul_inv_cancel, hA'.bd_one ξ hξS] at h4
      exact h4.symm
    calc bd (γ : PO n 1) ξ = bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) := by rw [h]
      _ = ξ := h3
  rw [Set.disjoint_left]
  intro u hu1 hu2
  simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
  -- `lev ξ u < s`
  have h1 : lev ξ u < s := by
    rw [lev_eq_exp hξS u, ← Real.exp_log hspos, Real.exp_lt_exp]
    exact hu1
  -- transport `hu2` to a level statement for `γ⁻¹ • u`
  have hbus := hI'.busemann_cocycle (γ : PO n 1) ξ ((γ : PO n 1)⁻¹ • u) hξS
  have hcoe : (γ : PO n 1) • ((γ : PO n 1)⁻¹ • u) = u := by
    rw [← hA'.mul_smul (γ : PO n 1) ((γ : PO n 1)⁻¹) u, mul_inv_cancel, hA'.one_smul]
  have hb : bCocy (γ : PO n 1) ξ
      = busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) := rfl
  rw [hcoe, ← hb] at hbus
  have h2 : busemann ξ ((γ : PO n 1)⁻¹ • u) < Real.log s := by linarith
  have h3 : lev ξ ((γ : PO n 1)⁻¹ • u) < s := by
    rw [lev_eq_exp hξS ((γ : PO n 1)⁻¹ • u), ← Real.exp_log hspos, Real.exp_lt_exp]
    exact h2
  have h4 := hs γ⁻¹ hne u h1
  have h4' : s ≤ lev ξ ((γ : PO n 1)⁻¹ • u) := by
    simpa only [Subgroup.coe_inv] using h4
  exact not_lt_of_ge h4' h3

/-- A level preserving element fixing `ξ` with vanishing Busemann cocycle is a flat translation of
the horospheres at `ξ`. -/
lemma lev_smul_of_bCocy_zero (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hfix : bd g ξ = ξ) (hc : bCocy g ξ = 0) :
    ∀ u : E n, lev ξ (g • u) = lev ξ u := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  intro u
  have hbus := hI'.busemann_cocycle g ξ u hξ
  have h0 : busemann ξ (g • (0 : E n)) = 0 := by
    have h1 : bCocy g ξ = busemann ξ (g • (0 : E n)) := by rw [bCocy, hfix]
    rw [← h1, hc]
  rw [hfix, h0, add_zero] at hbus
  rw [lev_eq_exp hξ (g • u), lev_eq_exp hξ u, hbus]

end

end Work.Mostow
