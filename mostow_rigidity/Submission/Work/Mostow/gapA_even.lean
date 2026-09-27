import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.frameThinFar
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.nilp_torsionGen_finite
import Submission.Work.Mostow.finite_shortAt
import Submission.Work.Mostow.KMcovol
import Submission.Work.Mostow.gaeEngine

/-!
# `gapA_even` — GAP-A (EscapeShort) for even `n ≥ 4`.

Assembled from `Work.Mostow.frameThinFar` (a nontrivial `η`-near-identity element outside
`Γ • K`) and `Work.Mostow.finTypeTubeEven` (the finite-type tube engine: a finite nontrivial
near-group forces `covol ≥ c η^{-α}` with `α > 0`).  The remaining step is group theory:
an infinite near-group is nilpotent (Zassenhaus) and finitely generated, so if it were
torsion it would be finite (`nilp_torsionGen_finite`); hence it contains an element of
infinite order, which is `η`-short at `z`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **Assembly, part 1 (numeric).** For `α > 0` there is `η > 0` with `c * η ^ (-α) > V`. -/
private lemma exists_eta_big {c α V : ℝ} (hc : 0 < c) (hα : 0 < α) (hV : 0 ≤ V) :
    ∃ η : ℝ, 0 < η ∧ c * η ^ (-α) > V := by
  refine ⟨(c / (2 * (V + 1))) ^ (1 / α), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  · have hx : 0 < c / (2 * (V + 1)) := by positivity
    rw [← Real.rpow_mul (le_of_lt hx)]
    have hexp : (1 / α) * (-α) = (-1 : ℝ) := by field_simp
    rw [hexp, Real.rpow_neg_one, inv_div]
    have hval : c * (2 * (V + 1) / c) = 2 * (V + 1) := by field_simp
    rw [hval]
    linarith

/-- **GAP-A for even `n ≥ 4`**, assembled from the finite-type tube engine
`finTypeTubeEven` and the near-identity escape `frameThinFar`. -/
theorem gapA_even (n : ℕ) (hn : 4 ≤ n) (hev : Even n)
    (hA : ∀ k, 2 ≤ k → POActionProp k) (hI : ∀ k, 2 ≤ k → HypIsometryProp k)
    (hCov : ∀ k, 2 ≤ k → k < n → CovolLB k)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (hmult : MultThickProp Γ) : GapAProp Γ := by
  obtain ⟨hdisc, D, hD, hDfin⟩ := hΓ
  obtain ⟨c, α, hcpos, hαpos, η₀, hη₀pos, hEngine⟩ := gaeTubeEven n hn hev hA hI hCov
  obtain ⟨η_Z, hηZpos, hηZ⟩ := zassenhausNilpotent n (by omega) (hA n (by omega)) (hI n (by omega))
  intro ε hε
  obtain ⟨η₁, hη₁pos, hη₁big⟩ := exists_eta_big (c := c) (α := α) (V := (volH n D).toReal) hcpos hαpos ENNReal.toReal_nonneg
  set η : ℝ := min (min ε η₀) (min η_Z η₁) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact lt_min (lt_min hε hη₀pos) (lt_min hηZpos hη₁pos)
  have hηε : η ≤ ε := by
    rw [hηdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hηη₀ : η ≤ η₀ := by
    rw [hηdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hηZle : η ≤ η_Z := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηη₁ : η ≤ η₁ := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hpow : η₁ ^ (-α) ≤ η ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hηpos hηη₁ (by linarith)
  have hgtV : c * η ^ (-α) > (volH n D).toReal :=
    lt_of_lt_of_le hη₁big (mul_le_mul_of_nonneg_left hpow (le_of_lt hcpos))
  have hbig : ENNReal.ofReal (c * η ^ (-α)) > volH n D := by
    rw [← ENNReal.ofReal_toReal hDfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hgtV
  obtain ⟨K, hKc, hK⟩ := frameThinFar n (by omega) (hA n (by omega)) (hI n (by omega)) Γ hdisc hmult η hηpos
  refine ⟨K, hKc, ?_⟩
  intro u hu
  obtain ⟨γ, hγne, hγnear⟩ := hK u hu
  have h0 : hdist u u ≤ 1 := by
    have hzero : hdist u u = 0 := ((hI n (by omega)).2.2.1 u u).mpr rfl
    rw [hzero]; norm_num
  have hFne : nearGrp Γ u η ≠ ⊥ := by
    intro hbot
    have hmem : (γ : PO n 1) ∈ nearGrp Γ u η :=
      Subgroup.subset_closure (show (γ : PO n 1) ∈ {g : PO n 1 | g ∈ Γ ∧ NearIdAt g u η} from
        ⟨γ.2, hγnear⟩)
    rw [hbot] at hmem
    exact hγne (Subtype.coe_injective (by simpa using hmem))
  by_cases hfin : Finite (nearGrp Γ u η)
  · exact absurd (hEngine η hηpos hηη₀ Γ D u hdisc hD hFne hfin) (not_le.mpr hbig)
  · set S : Set Γ := {γ : Γ | NearIdAt (γ : PO n 1) u η} with hSdef
    have hSfin : S.Finite :=
      (finite_shortAt n (hA n (by omega)) (hI n (by omega)) Γ hdisc u η).subset
        (fun γ hγ => le_of_lt (hγ u h0))
    set NG : Subgroup Γ := Subgroup.closure S with hNGdef
    have hnearGrp : nearGrp Γ u η = NG.map (Subgroup.subtype Γ) := by
      apply le_antisymm
      · rw [hNGdef,
          show nearGrp Γ u η = Subgroup.closure {g : PO n 1 | g ∈ Γ ∧ NearIdAt g u η} from rfl]
        refine (Subgroup.closure_le _).mpr ?_
        rintro g ⟨hgΓ, hgnear⟩
        exact Subgroup.mem_map_of_mem (Subgroup.subtype Γ)
          (Subgroup.subset_closure (show (⟨g, hgΓ⟩ : Γ) ∈ S from hgnear))
      · rw [hNGdef]
        refine (Subgroup.map_le_iff_le_comap).mpr ?_
        refine (Subgroup.closure_le _).mpr ?_
        rintro x hx
        show (x : PO n 1) ∈ nearGrp Γ u η
        rw [show nearGrp Γ u η = Subgroup.closure {g : PO n 1 | g ∈ Γ ∧ NearIdAt g u η} from rfl]
        exact Subgroup.subset_closure ⟨x.2, hx⟩
    have hkey : ∃ γ ∈ S, ¬ IsOfFinOrder γ := by
      by_contra hcon
      push_neg at hcon
      haveI : Finite ↑S := hSfin.to_subtype
      haveI hfg : Group.FG ↥NG := Group.closure_finite_fg S
      haveI hnil : Group.IsNilpotent ↥NG := by
        haveI : Group.IsNilpotent
            ↥(Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) u η_Z}) := hηZ Γ hdisc u
        refine isNilpotent_of_le (H := NG)
          (K := Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) u η_Z}) ?_
        rw [hNGdef]
        refine (Subgroup.closure_le _).mpr (fun x hx => Subgroup.subset_closure ?_)
        exact fun v hv => lt_of_lt_of_le (hx v hv) hηZle
      have hgen : Subgroup.closure {h : ↥NG | IsOfFinOrder h} = ⊤ :=
        closure_torsion_subtype_eq_top NG S rfl hcon
      haveI : Finite ↥NG := nilp_torsionGen_finite hgen
      have hfinmap : Finite ↥(NG.map (Subgroup.subtype Γ)) := by
        refine Finite.of_surjective
          (fun y : ↥NG => (⟨(y : PO n 1),
            Subgroup.mem_map_of_mem (Subgroup.subtype Γ) y.2⟩ :
              ↥(NG.map (Subgroup.subtype Γ)))) ?_
        intro x
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
        exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
      exact hfin (by rw [hnearGrp]; exact hfinmap)
    obtain ⟨γ, hγS, hγinf⟩ := hkey
    exact ⟨γ, orderOf_eq_zero_iff.mpr hγinf, lt_of_lt_of_le (hγS u h0) hηε⟩

end Work.Mostow
