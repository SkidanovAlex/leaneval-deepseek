import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Final.flatTwoTunableLinear

namespace Work.NN.Newton.FTedat

open scoped NNReal ENNReal ContDiff
open Set

/-- The components of the Bochner–Martinelli defect form `bmH χ η` are globally `C¹` when
`η` is `C¹` on the polydisc `polydisc 0 R`, `χ` is smooth and `tsupport χ` lies in the strictly
smaller polydisc `polydisc 0 r` (`r < R`). -/
lemma contDiff_bmH_of_tsupp {n : ℕ} {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (htsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 r)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ (1 : ℕ∞) (η i l) (Work.CR.Flat.polydisc 0 R))
    (j l i : Fin n) :
    ContDiff ℝ 1 (fun w => Work.NN.Core.bmH χ η j l i w) := by
  have hsd : ∀ a : Fin n, ContDiff ℝ ∞ (fun z => Work.CR.Flat.dbarCoord a χ z) :=
    fun a => Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a
  have hts : ∀ a : Fin n,
      tsupport (fun z => Work.CR.Flat.dbarCoord a χ z) ⊆ Work.CR.Flat.polydisc 0 R :=
    fun a => (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans
      (htsupp.trans (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hrR j))))
  have hprod : ∀ (a p q : Fin n),
      ContDiff ℝ 1 (fun z => Work.CR.Flat.dbarCoord a χ z * η p q z) :=
    fun a p q => Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport
      (Work.CR.Flat.isOpen_polydisc 0 R) (hsd a) (hts a) (hη p q)
  have heq : (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun z => Work.CR.Flat.dbarCoord i χ z * η j l z
          + Work.CR.Flat.dbarCoord j χ z * η l i z
          - Work.CR.Flat.dbarCoord l χ z * η j i z := by
    funext z; rw [Work.NN.Assemble.FT.bmH_eq_sum]
  rw [heq]
  exact ((hprod i j l).add (hprod j l i)).sub (hprod l j i)

/-- The defect form `bmH χ η` vanishes at a point at which some coordinate dominates the
corresponding radius `R`, provided `tsupport χ ⊆ polydisc 0 r` with `r < R`. -/
lemma bmH_eq_zero_of_coord_le {n : ℕ} {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ}
    (htsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 r)
    (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (j l i : Fin n) {z : Fin n → ℂ}
    (hz : ∃ a, R a ≤ ‖z a‖) : Work.NN.Core.bmH χ η j l i z = 0 := by
  obtain ⟨a, ha⟩ := hz
  have hzr : z ∉ Work.CR.Flat.polydisc 0 r := by
    intro hzP
    have h1 : ‖z a‖ < r a := by simpa using hzP a
    have h2 := hrR a
    linarith
  have hzt : z ∉ tsupport χ := fun h => hzr (htsupp h)
  have h0 : ∀ p : Fin n, Work.CR.Flat.dbarCoord p χ z = 0 := fun p => by
    by_contra hp
    exact hzt ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset p)
      (subset_tsupport (fun z => Work.CR.Flat.dbarCoord p χ z)
        (Function.mem_support.mpr hp)))
  rw [Work.NN.Assemble.FT.bmH_eq_sum, h0 i, h0 j, h0 l]
  ring

theorem Edat_gain_expl {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R T : Fin n → ℝ} (hRpos : ∀ j, 0 < R j) (hrR : ∀ j, r j < R j) (hTR : ∀ j, T j ≤ R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 r)
    {Ch Cg : ℝ} (hCh : 0 < Ch) (hCg : 0 < Cg)
    (hbmH : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ (1 : ℕ∞) (η i l) (Work.CR.Flat.polydisc 0 R)) → ∀ j l i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
          ≤ ENNReal.ofReal Ch * ∑ a : Fin n, ∑ b : Fin n,
              Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R))
    (hCg' : ∀ g : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiff ℝ 1 (g j)) → (∀ j, HasCompactSupport (g j)) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ < ⊤) →
      (∀ j z, (∃ i, R i ≤ ‖z i‖) → g j z = 0) →
      ContDiffOn ℝ (1 : ℕ∞) (Work.CR.Flat.Cauchy.bmPot g) (Work.CR.Flat.polydisc 0 R) ∧
      Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPot g) (Work.CR.Flat.polydisc 0 R)
        ≤ ENNReal.ofReal Cg * ∑ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ) :
    ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ (1 : ℕ∞) (η i l) (Work.CR.Flat.polydisc 0 R)) → ∀ j l : Fin n,
        Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
            (Work.CR.Flat.polydisc 0 T)
          ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch) + 1)
              * ∑ a : Fin n, ∑ b : Fin n,
                  Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R) := by
  intro η hη j l
  set S : ℝ≥0∞ := ∑ a : Fin n, ∑ b : Fin n,
      Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R) with hSdef
  let c : ℂ := (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
  let g : Fin n → (Fin n → ℂ) → ℂ := fun i => Work.NN.Core.bmH χ η j l i
  have hcd : ∀ i, ContDiff ℝ 1 (g i) :=
    fun i => contDiff_bmH_of_tsupp hrR hχ htsupp hη j l i
  have hcsg : ∀ i, HasCompactSupport (g i) :=
    fun i => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs j l i
  have hfin : ∀ i, Work.CR.Flat.holderNorm 0 α (g i) Set.univ < ⊤ :=
    fun i => Work.NN.Core.holderNorm_zero_univ_lt_top_of_contDiff_one hα0 hα1 (hcd i) (hcsg i)
  have hvan : ∀ i z, (∃ a, R a ≤ ‖z a‖) → g i z = 0 :=
    fun i z hz => bmH_eq_zero_of_coord_le hrR htsupp η j l i hz
  obtain ⟨hp, hb⟩ := hCg' g hcd hcsg hfin hvan
  have hEdat : Work.NN.Assemble.FT.Edat χ η j l = c • (Work.CR.Flat.Cauchy.bmPot g) := by
    funext z
    rw [Work.NN.Assemble.FT.Edat_apply]
    rfl
  have hmono : Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
        (Work.CR.Flat.polydisc 0 T)
      ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
        (Work.CR.Flat.polydisc 0 R) :=
    Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 R)
      (Work.CR.Flat.isOpen_polydisc 0 T) (Work.CR.Flat.polydisc_mono (fun j => hTR j)) 1 α _
  have hsmul : Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
        (Work.CR.Flat.polydisc 0 R)
      = ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPot g)
        (Work.CR.Flat.polydisc 0 R) := by
    rw [hEdat]
    exact Work.CR.Flat.Holder.holderNorm_smul c hp
      (Work.CR.Flat.isOpen_polydisc 0 R).uniqueDiffOn
  have hsum_le : (∑ i : Fin n, Work.CR.Flat.holderNorm 0 α (g i) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * Ch) * S := by
    calc ∑ i : Fin n, Work.CR.Flat.holderNorm 0 α (g i) Set.univ
        ≤ ∑ _i : Fin n, (ENNReal.ofReal Ch * S) := by
          refine Finset.sum_le_sum fun i _ => ?_
          simpa [hSdef] using hbmH η hη j l i
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal Ch * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * Ch) * S := by
          rw [← ENNReal.ofReal_natCast n, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
        (Work.CR.Flat.polydisc 0 T)
      ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l)
        (Work.CR.Flat.polydisc 0 R) := hmono
    _ = ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPot g)
        (Work.CR.Flat.polydisc 0 R) := hsmul
    _ ≤ ENNReal.ofReal ‖c‖ *
          (ENNReal.ofReal Cg * ∑ i : Fin n, Work.CR.Flat.holderNorm 0 α (g i) Set.univ) :=
        mul_le_mul_right hb _
    _ ≤ ENNReal.ofReal ‖c‖ *
          (ENNReal.ofReal Cg * (ENNReal.ofReal ((n : ℝ) * Ch) * S)) :=
        mul_le_mul_right (mul_le_mul_right hsum_le _) _
    _ = ENNReal.ofReal (‖c‖ * Cg * ((n : ℝ) * Ch)) * S := by
        rw [← mul_assoc (ENNReal.ofReal ‖c‖) (ENNReal.ofReal Cg)
              (ENNReal.ofReal ((n : ℝ) * Ch) * S),
            ← mul_assoc (ENNReal.ofReal ‖c‖ * ENNReal.ofReal Cg)
              (ENNReal.ofReal ((n : ℝ) * Ch)) S,
            ← ENNReal.ofReal_mul (norm_nonneg c),
            ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (‖c‖ * Cg * ((n : ℝ) * Ch) + 1) * S :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) S

end Work.NN.Newton.FTedat
