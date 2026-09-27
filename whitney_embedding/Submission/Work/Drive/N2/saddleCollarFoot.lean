import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# Collar constancy: a model whose square depends only on `Im z²` is constant along the collar
trajectories

The flow lines of the saddle model field `X₀ = (u, -v)/(2|z|²)` are the sets `{Im z² = const}`.  A
model `Ψ : ℂ → ℂ` whose *square* depends only on `Im z²` on a collar is therefore **constant along
the (continuous pieces of the) flow lines of `X₀` in that collar**.  This is the "well-definedness of
the picture `A`" input of the window gluing (`NOTES_S_NEXT_window_matching_CRUX.md` §7, (T2)):  on
the foot image of the collar the picture of the anchor level has to be *defined* by
`A (foot x) := Ψ (Z x)`, and that is legitimate exactly because `Ψ` does not change along the
trajectories that the flow transport follows.

The general form `collarConstancy_of_sq_depends_on_im` is stated for an *arbitrary* `Ψ` and an
arbitrary collar `C`: the only hypothesis is `(Ψ z)² = P ((z²).im)` on `C`, i.e. that the square of
the model is a function of `Im z²` there.  The proof is soft: along a path in `C` on which `Im z²`
is constant, `(Ψ (γ ·))²` is constant and non-zero, so the continuous image of the preconnected
parameter interval lies in the two-point set `{c, -c}` and is a single point.

The instance for the saddle model `saddlePsi` of `saddleModelPsi.lean` (`saddlePsi_collar`) is
recorded at the end, in the plane and in the chart form.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- **Collar constancy, abstract form.**  If `Ψ` is any function whose square is a function of
`Im z²` on a set `C`, and `γ` is a continuous path in `C` on which `Im z²` is constant, then `Ψ` is
constant along `γ`. -/
theorem collarConstancy_of_sq_depends_on_im {Ψ : ℂ → ℂ} {C : Set ℂ} {P : ℝ → ℂ} {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0:ℝ) 1)) (hγC : ∀ s ∈ Icc (0:ℝ) 1, γ s ∈ C)
    (hΨc : ContinuousOn Ψ C)
    (hP : ∀ z ∈ C, (Ψ z) ^ 2 = P ((z ^ 2).im))
    (him : ∀ s ∈ Icc (0:ℝ) 1, ((γ s) ^ 2).im = ((γ 0) ^ 2).im)
    (hne : (Ψ (γ 0)) ^ 2 ≠ 0) :
    Ψ (γ 1) = Ψ (γ 0) := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  set c : ℂ := Ψ (γ 0)
  have hsq : ∀ s ∈ Icc (0:ℝ) 1, Ψ (γ s) ^ 2 = c ^ 2 := by
    intro s hs
    rw [hP (γ s) (hγC s hs), hP (γ 0) (hγC 0 h0), him s hs]
  have hcne : c ≠ 0 := fun h => hne (by rw [h]; ring)
  have hcne' : c ≠ -c := fun h => hcne (add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp h))
  have hmaps : MapsTo (fun s => Ψ (γ s)) (Icc (0:ℝ) 1) ({c, -c} : Set ℂ) := by
    intro s hs
    have hfac : (Ψ (γ s) - c) * (Ψ (γ s) + c) = 0 := by
      have hzero : Ψ (γ s) ^ 2 - c ^ 2 = 0 := by rw [hsq s hs]; ring
      rw [← hzero]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcont : ContinuousOn (fun s => Ψ (γ s)) (Icc (0:ℝ) 1) :=
    hΨc.comp hγ hγC
  have hT : IsDiscrete ({c, -c} : Set ℂ) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · refine ⟨{z : ℂ | z ≠ -c}, isOpen_ne, ?_⟩
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · intro h
        exact ⟨fun hc => hcne' (h.symm.trans hc), Or.inl h⟩
    · refine ⟨{z : ℂ | z ≠ c}, isOpen_ne, ?_⟩
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd h2 h1
        · exact h2
      · intro h
        exact ⟨fun hc => hcne' (hc.symm.trans h), Or.inr h⟩
  exact isPreconnected_Icc.constant_of_mapsTo hT hcont hmaps h1 h0

/-- The collar of the saddle model in the plane: `|Re z²| ≤ η` and `2 - 2δ ≤ |Im z²| ≤ 2`. -/
def saddleCollar (η δ : ℝ) : Set ℂ :=
  {z | |(z ^ 2).re| ≤ η ∧ 2 - 2 * δ ≤ |(z ^ 2).im| ∧ |(z ^ 2).im| ≤ 2}

/-- `saddlePsi_collar` restated as "the square of the model is a function of `Im z²`". -/
theorem saddlePsi_sq_depends_on_im {η δ : ℝ} (hη : 0 < η) (hη' : η < 1/10) (hδ : 0 < δ)
    (hδ' : δ < 1/10) :
    ∀ z, z ∈ saddleCollar η δ →
      (saddlePsi η δ z) ^ 2 = -(η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I :=
  fun z hz => (saddlePsi_collar hη hη' hδ hδ' hz.1 hz.2.1 hz.2.2).1

/-- **Collar constancy of the saddle model.**  Let `γ : ℝ → ℂ` be a continuous path whose
restriction to `[0,1]` lies in the collar and along which `Im (γ ·)²` is constant.  Then
`saddlePsi η δ` takes the same value at `γ 0` and `γ 1`. -/
theorem saddlePsi_collar_eq_of_continuousOn {η δ : ℝ} (hη : 0 < η) (hη' : η < 1/10) (hδ : 0 < δ)
    (hδ' : δ < 1/10) {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0:ℝ) 1))
    (hγC : ∀ s ∈ Icc (0:ℝ) 1, γ s ∈ saddleCollar η δ)
    (him : ∀ s ∈ Icc (0:ℝ) 1, ((γ s) ^ 2).im = ((γ 0) ^ 2).im) :
    saddlePsi η δ (γ 1) = saddlePsi η δ (γ 0) := by
  have h2 : (0:ℝ) < 2 - 4 * δ := by linarith
  have hne : (saddlePsi η δ (γ 0)) ^ 2 ≠ 0 := by
    rw [saddlePsi_sq_depends_on_im hη hη' hδ hδ' (γ 0) (hγC 0 ⟨le_rfl, by norm_num⟩)]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  exact collarConstancy_of_sq_depends_on_im (P := fun w : ℝ => -(η : ℂ) + (w : ℂ) * Complex.I)
    hγ hγC ((contDiff_saddlePsi η δ hδ (by linarith)).continuous.continuousOn)
    (saddlePsi_sq_depends_on_im hη hη' hδ hδ') him hne

/-- **Collar constancy of the saddle model (chart form).**  If `Z` is a chart coordinate of a
saddle and `γ` is a continuous path in the collar of `Z` along which `Im (Z ·)²` is constant, then
the model drawing `x ↦ saddlePsi η δ (Z x)` is constant along `γ`. -/
theorem saddlePsi_collar_eq_of_continuousOn_comp {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {U : Set M} {Z : M → ℂ}
    (hZ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    {γ : ℝ → M} (hγ : ContinuousOn γ (Icc (0:ℝ) 1))
    (hγU : ∀ s ∈ Icc (0:ℝ) 1, γ s ∈ U)
    {η δ : ℝ} (hη : 0 < η) (hη' : η < 1/10) (hδ : 0 < δ) (hδ' : δ < 1/10)
    (hγC : ∀ s ∈ Icc (0:ℝ) 1, Z (γ s) ∈ saddleCollar η δ)
    (him : ∀ s ∈ Icc (0:ℝ) 1, ((Z (γ s)) ^ 2).im = ((Z (γ 0)) ^ 2).im) :
    saddlePsi η δ (Z (γ 1)) = saddlePsi η δ (Z (γ 0)) :=
  saddlePsi_collar_eq_of_continuousOn hη hη' hδ hδ' (hZ.continuousOn.comp hγ hγU) hγC
    (fun s hs => him s hs)

end Work.Drive.N2
