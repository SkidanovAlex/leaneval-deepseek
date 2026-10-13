import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6
import Submission.Work.FTS.StrongEps.LocUnif.D5.rounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.LocUnif

/-- **The level-5 extraction.**  From the uniform convergence of all the slots `D_z^jD_θ^i` with
`j + i ≤ 4` (together with the uniform `H⁶` bound and the `C⁴` regularity of the limit `f`) there
is a further strictly increasing subsequence `φ'` along which every level-5 slot
`D_z^jD_θ^i` (`j + i = 5`) converges to the corresponding slot of `f` almost everywhere on the
open quadrant.

Each level-5 slot is one derivative (in `z` when `j ≥ 1`, in `θ` when `j = 0`) of a level-4 slot;
the extraction is done one slot at a time (`D5.round_slot`), each round using the exhaustion
`Q0 = ⋃ m, eBox m` of the quadrant by compact boxes and a diagonal subsequence argument. -/
theorem exists_subseq_deriv5_ae {α B : ℝ} (hα : 0 < α)
    {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hconv0 : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => G (φ n) p.1 p.2) (fun p => f p.1 p.2)
        Filter.atTop K)
    (hconv4 : ∀ (j i : ℕ), j + i ≤ 4 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => Work.Spaces.mixed j i (G (φ n)) p.1 p.2)
        (fun p => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K)
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧
      ∀ (j i : ℕ), j + i = 5 →
        ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))),
          Filter.Tendsto (fun n => Work.Spaces.mixed j i (G (φ (φ' n))) p.1 p.2)
            Filter.atTop (nhds (Work.Spaces.mixed j i f p.1 p.2)) := by
  classical
  have hsm' : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n) :=
    fun n => Work.FTS.EllipticEst.smoothOpen_of_forall (hsm n)
  obtain ⟨Φ₀, hΦ₀, H₀⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 5) (i := 0) (by norm_num) (τ := id) strictMono_id
  obtain ⟨Φ₁, hΦ₁, H₁⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 4) (i := 1) (by norm_num) (τ := Φ₀) hΦ₀
  obtain ⟨Φ₂, hΦ₂, H₂⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 3) (i := 2) (by norm_num) (τ := Φ₀ ∘ Φ₁) (hΦ₀.comp hΦ₁)
  obtain ⟨Φ₃, hΦ₃, H₃⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 2) (i := 3) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂)
    (hΦ₀.comp (hΦ₁.comp hΦ₂))
  obtain ⟨Φ₄, hΦ₄, H₄⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 1) (i := 4) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃)
    (hΦ₀.comp (hΦ₁.comp (hΦ₂.comp hΦ₃)))
  obtain ⟨Φ₅, hΦ₅, H₅⟩ := D5.round_slot (α := α) (B := B) (G := G) (φ := φ) (f := f)
    hα hsm' hmem hb hconv4 (j := 0) (i := 5) (by norm_num) (τ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄)
    (hΦ₀.comp (hΦ₁.comp (hΦ₂.comp (hΦ₃.comp hΦ₄))))
  -- the tails of the tower
  have htail₅ : StrictMono (Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) :=
    hΦ₁.comp (hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅)))
  have htail₄ : StrictMono (Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) := hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅))
  have htail₃ : StrictMono (Φ₃ ∘ Φ₄ ∘ Φ₅) := hΦ₃.comp (hΦ₄.comp hΦ₅)
  have htail₂ : StrictMono (Φ₄ ∘ Φ₅) := hΦ₄.comp hΦ₅
  have htail₁ : StrictMono Φ₅ := hΦ₅
  set Φf : ℕ → ℕ := Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅ with hΦf
  have hΦf_mono : StrictMono Φf := by
    rw [hΦf]
    exact hΦ₀.comp (hΦ₁.comp (hΦ₂.comp (hΦ₃.comp (hΦ₄.comp hΦ₅))))
  -- the six slots, re-indexed by the full tower
  have hfin₀ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 5 0 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 5 0 f p.1 p.2)) := fun m => by
    filter_upwards [H₀ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 5 0 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 5 0 (G (φ (id (Φ₀ n)))) p.1 p.2)
          ∘ (Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf, id_eq]]
    exact (hp hm).comp htail₅.tendsto_atTop
  have hfin₁ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 4 1 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 4 1 f p.1 p.2)) := fun m => by
    filter_upwards [H₁ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 4 1 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 4 1 (G (φ (Φ₀ (Φ₁ n)))) p.1 p.2)
          ∘ (Φ₂ ∘ Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₄.tendsto_atTop
  have hfin₂ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 3 2 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 3 2 f p.1 p.2)) := fun m => by
    filter_upwards [H₂ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 3 2 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 3 2 (G (φ ((Φ₀ ∘ Φ₁) (Φ₂ n)))) p.1 p.2)
          ∘ (Φ₃ ∘ Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₃.tendsto_atTop
  have hfin₃ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 2 3 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 2 3 f p.1 p.2)) := fun m => by
    filter_upwards [H₃ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 2 3 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 2 3 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂) (Φ₃ n)))) p.1 p.2)
          ∘ (Φ₄ ∘ Φ₅) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₂.tendsto_atTop
  have hfin₄ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 1 4 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 1 4 f p.1 p.2)) := fun m => by
    filter_upwards [H₄ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 1 4 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 1 4 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃) (Φ₄ n)))) p.1 p.2)
          ∘ Φ₅ from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact (hp hm).comp htail₁.tendsto_atTop
  have hfin₅ : ∀ m : ℕ, ∀ᵐ p ∂(MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0),
      p ∈ D5.eBox m →
        Filter.Tendsto (fun n => Work.Spaces.mixed 0 5 (G (φ (Φf n))) p.1 p.2)
          Filter.atTop (nhds (Work.Spaces.mixed 0 5 f p.1 p.2)) := fun m => by
    filter_upwards [H₅ m] with p hp hm
    rw [show (fun n => Work.Spaces.mixed 0 5 (G (φ (Φf n))) p.1 p.2)
        = (fun n => Work.Spaces.mixed 0 5 (G (φ ((Φ₀ ∘ Φ₁ ∘ Φ₂ ∘ Φ₃ ∘ Φ₄) (Φ₅ n))))
            p.1 p.2) from by
      funext n; simp only [Function.comp_apply, hΦf]]
    exact hp hm
  refine ⟨Φf, hΦf_mono, ?_⟩
  intro j i hji
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · -- the slot `(0, 5)`
    have hi : i = 5 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₅
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(1, 4)`
    have hi : i = 4 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₄
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(2, 3)`
    have hi : i = 3 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₃
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(3, 2)`
    have hi : i = 2 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₂
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(4, 1)`
    have hi : i = 1 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₁
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm
  · -- the slot `(5, 0)`
    have hi : i = 0 := by omega
    subst hi
    have hall := MeasureTheory.ae_all_iff.mpr hfin₀
    filter_upwards [hall,
      MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet] with p hp hQ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (by rw [D5.iUnion_eBox]; exact hQ)
    exact hp m hm

end Work.FTS.StrongEps.LocUnif
