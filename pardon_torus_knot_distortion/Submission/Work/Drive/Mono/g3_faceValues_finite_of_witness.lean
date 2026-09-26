import Mathlib
import Submission.Work.Drive.Mono.g3WitnessDefs
import Submission.Work.Drive.Mono.finite_facePts_tilted
import Submission.Work.Drive.Mono.geom3Extra

/-!
# The `ℓ`-values of the knot's face points inside the Pardon box lie in a finite set

`Work.Drive.Mono.WitnessData3` says, among many other things, that inside the open Pardon box
`PBox s c σ` the tilted height `slabFn c u V ∘ K` of the knot has nonvanishing derivative at every
parameter at which it takes the value `±h` (for `h` in the window `(A, B)`), and that on the *box
sphere* `{boxNorm = s}` the absolute tilted height is at least any such `h`.

The second clause turns the *open* box condition of the first into a closed one: if `t` lies in one
period, in the closed box and on the level `|slabFn| = h`, then in fact `boxNorm (K t) < s`, because
`boxNorm (K t) = s` together with the same clause at a larger `h' ∈ (h, B)` would give the
contradiction `h' ≤ h`.  Hence every such parameter lies in the open box, the derivative does not
vanish there, and the points of the set are isolated.  Compactness of one period intersected with
the closed box then makes the parameter set finite, and the finitely many `ℓ`-values of these
parameters give the required `Finset`.

-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-- Every point of a `2π`-periodic curve is attained at a parameter in the half-open fundamental
period `[0, 2π)`. -/
private theorem exists_mem_Ico_of_periodic_local {α : Type*} {f : ℝ → α}
    (hf : Function.Periodic f (2 * Real.pi)) (t : ℝ) :
    ∃ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), f s = f t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi' : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
  refine ⟨t - (⌊t / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi), ?_, hf.sub_int_mul_eq _⟩
  rw [Set.mem_Ico]
  have hlo := Int.floor_le (t / (2 * Real.pi))
  have hup := Int.lt_floor_add_one (t / (2 * Real.pi))
  have h1 : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ t := by
    have hm := mul_le_mul_of_nonneg_right hlo (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ hpi'] at hm
  have h2 : t < ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + (2 * Real.pi) := by
    have hm := mul_lt_mul_of_pos_right hup hpi
    rw [add_mul, one_mul, div_mul_cancel₀ _ hpi'] at hm
    linarith
  exact ⟨by linarith, by linarith⟩

theorem g3_faceValues_finite_of_witness
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {s u : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (V n a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (ρ A B : ℝ) (N : ℕ)
    (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m δg mE : ℝ)
    (hW : Work.Drive.Mono.WitnessData3 ψ K s u c σ V n a₀ b₀ ρ A B N γ η m δg mE)
    (h : ℝ) (hh : h ∈ Set.Ioo A B) (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) :
    ∃ exc : Finset ℝ, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u V (K.curve t)| = h → ℓ (K.curve t) ∈ (exc : Set ℝ) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hApos, hAB, _, _, _, _, _, hsphere, _, _, hface, _,
    _, _, _, _, _, _, _, _, _, _⟩ := hW
  have hhpos : 0 < h := lt_trans hApos hh.1
  -- * the signed tilted height of the knot, as a function of the parameter
  have hcont : Continuous (fun t : ℝ => Work.Drive.Final.slabFn c u V (K.curve t)) := by
    have heq : (fun t : ℝ => Work.Drive.Final.slabFn c u V (K.curve t))
        = fun t : ℝ => inner ℝ V (K.curve t) - (inner ℝ V c + u) := by
      funext t; rw [Work.Drive.Final.slabFn_apply]
    rw [heq]
    exact (continuous_const.inner K.smooth.continuous).sub continuous_const
  have hdg : ∀ t : ℝ, deriv (fun r : ℝ => Work.Drive.Final.slabFn c u V (K.curve r)) t
      = inner ℝ V (deriv K.curve t) := by
    intro t
    have heq : (fun r : ℝ => Work.Drive.Final.slabFn c u V (K.curve r))
        = fun r : ℝ => inner ℝ V (K.curve r) - (inner ℝ V c + u) := by
      funext r; rw [Work.Drive.Final.slabFn_apply]
    rw [heq, deriv_sub_const, Work.Drive.Mono.deriv_inner_curve_const]
  have hdgcont : Continuous (deriv (fun r : ℝ => Work.Drive.Final.slabFn c u V (K.curve r))) := by
    have heq : deriv (fun r : ℝ => Work.Drive.Final.slabFn c u V (K.curve r))
        = fun t : ℝ => inner ℝ V (deriv K.curve t) := funext hdg
    rw [heq]
    exact continuous_const.inner (Work.Drive.Mono.contDiff_deriv_curve K).continuous
  -- * the parameter set of interest in one period
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
    Submission.boxNorm c σ (K.curve t) ≤ s ∧
    |Work.Drive.Final.slabFn c u V (K.curve t)| = h} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧
      |Work.Drive.Final.slabFn c u V (K.curve t)| = h := by
    intro t; simp only [hSdef, Set.mem_ofPred_eq]
  -- * no point of `S` lies on the box sphere
  have hlt_of_mem : ∀ t ∈ S, Submission.boxNorm c σ (K.curve t) < s := by
    intro t ht
    obtain ⟨-, hbox, habs⟩ := (hSmem t).mp ht
    rcases lt_or_eq_of_le hbox with hlt | heq
    · exact hlt
    · exfalso
      have hmid : (h + B) / 2 ∈ Set.Ioo A B := ⟨by linarith [hh.1], by linarith [hh.2]⟩
      have hle : (h + B) / 2 ≤ |Work.Drive.Final.slabFn c u V (K.curve t)| :=
        hsphere ((h + B) / 2) hmid t heq
      rw [habs] at hle
      linarith [hh.2]
  -- * every point of `S` has a neighbourhood meeting `S` in at most two points
  have hloc : ∀ x ∈ S, ∃ U : Set ℝ, U ∈ nhds x ∧ (S ∩ U).Finite := by
    intro x hx
    obtain ⟨-, -, hxabs⟩ := (hSmem x).mp hx
    have hxlt : Submission.boxNorm c σ (K.curve x) < s := hlt_of_mem x hx
    have hPBox : K.curve x ∈ Submission.PBox s c σ :=
      (Submission.mem_PBox_iff s c σ (K.curve x)).mpr hxlt
    have hdx : inner ℝ V (deriv K.curve x) ≠ 0 := by
      rw [← Work.Drive.Mono.deriv_inner_curve_const K V x]
      exact hface h hh x hPBox hxabs
    have hopen : IsOpen {y : ℝ | inner ℝ V (deriv K.curve y) ≠ 0} :=
      isOpen_compl_singleton.preimage
        (continuous_const.inner (Work.Drive.Mono.contDiff_deriv_curve K).continuous)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hdx)
    refine ⟨Set.Ioo (x - ε) (x + ε), isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩, ?_⟩
    have hsub : Set.Ioo (x - ε) (x + ε) ⊆ {y : ℝ | inner ℝ V (deriv K.curve y) ≠ 0} := by
      intro y hy
      exact hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_sub_lt_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    have hinj : Set.InjOn (fun r : ℝ => Work.Drive.Final.slabFn c u V (K.curve r))
        (Set.Ioo (x - ε) (x + ε)) := by
      apply Work.Drive.Mono.intervalZeros.injOn_of_deriv_ne_zero (by linarith : x - ε < x + ε)
      intro y hy
      rw [hdg y]
      exact hsub hy
    have hsingle1 : Set.Subsingleton {y : ℝ | y ∈ Set.Ioo (x - ε) (x + ε) ∧
        Work.Drive.Final.slabFn c u V (K.curve y) = h} := by
      intro y₁ hy₁ y₂ hy₂
      exact hinj hy₁.1 hy₂.1 (by simp only [hy₁.2, hy₂.2])
    have hsingle2 : Set.Subsingleton {y : ℝ | y ∈ Set.Ioo (x - ε) (x + ε) ∧
        Work.Drive.Final.slabFn c u V (K.curve y) = -h} := by
      intro y₁ hy₁ y₂ hy₂
      exact hinj hy₁.1 hy₂.1 (by simp only [hy₁.2, hy₂.2])
    refine Set.Finite.subset ((Set.Subsingleton.finite hsingle1).union
      (Set.Subsingleton.finite hsingle2)) ?_
    rintro y ⟨hyS, hyI⟩
    obtain ⟨-, -, hyabs⟩ := (hSmem y).mp hyS
    rcases (abs_eq hhpos.le).mp hyabs with hy | hy
    · exact Or.inl ⟨hyI, hy⟩
    · exact Or.inr ⟨hyI, hy⟩
  -- * `S` is a closed subset of a compact interval
  have hclosed : IsClosed S := by
    have h1 : IsClosed (Set.Icc (0 : ℝ) (2 * Real.pi)) := isClosed_Icc
    have h2 : IsClosed {t : ℝ | Submission.boxNorm c σ (K.curve t) ≤ s} :=
      isClosed_le ((Work.Topology.SphereSlicing.boxNorm_continuous c σ).comp K.smooth.continuous)
        continuous_const
    have h3 : IsClosed {t : ℝ | |Work.Drive.Final.slabFn c u V (K.curve t)| = h} :=
      isClosed_eq (continuous_abs.comp hcont) continuous_const
    have heq : S = Set.Icc (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | Submission.boxNorm c σ (K.curve t) ≤ s} ∩
        {t : ℝ | |Work.Drive.Final.slabFn c u V (K.curve t)| = h} := by
      ext t
      simp only [hSdef, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
    exact (h1.inter h2).inter h3
  have hSsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) := fun t ht => ((hSmem t).mp ht).1
  have hScomp : IsCompact S := IsCompact.of_isClosed_subset isCompact_Icc hclosed hSsub
  -- * hence finite
  have hfinS : S.Finite := by
    obtain ⟨F, hFsub, hFcover⟩ := hScomp.elim_nhds_subcover
      (fun x => if hx : x ∈ S then Classical.choose (hloc x hx) else Set.univ)
      (fun x hx => by rw [dif_pos hx]; exact (Classical.choose_spec (hloc x hx)).1)
    have hcov : S ⊆ ⋃ x ∈ (F : Set ℝ),
        (S ∩ (if hx : x ∈ S then Classical.choose (hloc x hx) else Set.univ)) := by
      intro y hy
      obtain ⟨x, hxF, hyU⟩ := by simpa only [Set.mem_iUnion] using hFcover hy
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxF, hy, hyU⟩⟩
    refine Set.Finite.subset
      (Set.Finite.biUnion (Finset.finite_toSet F) (fun x hx => ?_)) hcov
    have hxS : x ∈ S := hFsub x hx
    rw [dif_pos hxS]
    exact (Classical.choose_spec (hloc x hxS)).2
  -- * the finitely many `ℓ`-values of `S`
  refine ⟨hfinS.toFinset.image (fun t : ℝ => ℓ (K.curve t)), ?_⟩
  intro t htPBox htab
  obtain ⟨t', ht'I, ht'eq⟩ := exists_mem_Ico_of_periodic_local K.periodic t
  have ht'S : t' ∈ S := by
    refine (hSmem t').mpr ⟨⟨ht'I.1, le_of_lt ht'I.2⟩, ?_, ?_⟩
    · rw [ht'eq]
      exact le_of_lt ((Submission.mem_PBox_iff s c σ (K.curve t)).mp htPBox)
    · rw [ht'eq]
      exact htab
  have hmem : ℓ (K.curve t') ∈ hfinS.toFinset.image (fun t : ℝ => ℓ (K.curve t)) :=
    Finset.mem_image.mpr ⟨t', (Set.Finite.mem_toFinset hfinS).mpr ht'S, rfl⟩
  simpa only [ht'eq, Finset.mem_coe] using hmem

end

end Work.Drive.Mono
