import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.jordan_compl_atMostTwo
import Submission.Work.Smooth.SphereJordan.twoComponentsAux
import Submission.Work.Smooth.SphereJordan.openImage_isOpen
import Submission.Work.Smooth.SphereJordan.planeArcComponentsCore
import Submission.Work.Smooth.SphereJordan.disc_openImage_subset_boundedSide

/-!
# The complement of an embedded disc in the plane is preconnected

Let `f : 𝔻 → ℂ` be continuous and injective, so that `X := range f` is an embedded closed disc in the
plane.  We prove that `Xᶜ` is preconnected.

## The structure of the proof

Write `O := openImage f = f '' {z | ‖z‖ < 1}` (the image of the *open* disc, which is open in `ℂ`
by invariance of domain, `openImage_isOpen`) and let `C` be the trace of the simple closed curve
`γ : θ ↦ f (e^{iθ})` (the boundary of the disc).  The image decomposes as

  `range f = O ∪ C`,  with `O ∩ C = ∅`   (`range_eq_openImage_union_circleImage`),

so that

  `Cᶜ = O ⊔ (range f)ᶜ`   (`compl_range_circlePoint_eq`)

is a disjoint union of two **open** (in `ℂ`) sets.  Both are nonempty: `f 0 ∈ O` and `(range f)ᶜ ≠ ∅`
because `range f` is bounded.

The remaining — classical — input is the *at most two components* half of the Jordan curve theorem
(`jordan_compl_atMostTwo_aux`; delegated): the complement of the trace of a simple closed plane curve
has at most two connected components.  Now `O` is preconnected (`openImage_preconnected`), so it is
contained in a single component of `Cᶜ`; and since `Cᶜ` has at most two components, the clopen set
`(range f)ᶜ` must be a single component as well:

if `y, z ∈ (range f)ᶜ` lay in two different components of `Cᶜ`, then together with `f 0 ∈ O` we would
have three points of `Cᶜ` no two of which share a component of `Cᶜ`, contradicting the at-most-two
statement.  The key point is that a preconnected subset of `Cᶜ = O ∪ (range f)ᶜ`, covered by the two
disjoint *open* sets `O` and `(range f)ᶜ`, lies in one of them
(`IsPreconnected.subset_left_of_subset_union`), so a component containing a point of `(range f)ᶜ`
cannot meet `O`.

Hence `(range f)ᶜ` is a `connectedComponentIn` of `Cᶜ`, and connected components are preconnected.

## Main result

* `Work.Smooth.SphereJordan.compl_range_disc_preconnected_plane`
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## The boundary circle -/

/-- **`circlePoint` is injective on one period `[0, 2π)`.**  Two parameters in `[0, 2π)` differ by
less than `2π`, so `circlePoint_injOn_Icc` applies. -/
theorem circlePoint_injOn_Ico_period :
    Set.InjOn (circlePoint : ℝ → Disc) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · have h1 : b - a < 2 * Real.pi := by
      have := hb.2; have := ha.1; linarith
    exact absurd (circlePoint_injOn_Icc (x := a) (y := b) h1
      ⟨le_refl a, le_of_lt h⟩ ⟨le_of_lt h, le_refl b⟩ hab) (ne_of_lt h)
  · exact h
  · have h1 : a - b < 2 * Real.pi := by
      have := ha.2; have := hb.1; linarith
    exact absurd (circlePoint_injOn_Icc (x := b) (y := a) h1
      ⟨le_refl b, le_of_lt h⟩ ⟨le_of_lt h, le_refl a⟩ hab.symm) (ne_of_lt h)

/-- The image of the boundary circle of the model disc under `f`. -/
def circleImage (f : C(Disc, ℂ)) : Set ℂ := f '' {z : Disc | ‖(z : ℂ)‖ = 1}

/-- The boundary circle image is the trace of the `2π`-periodic curve `θ ↦ f (e^{iθ})`. -/
theorem circleImage_eq_range_circlePoint (f : C(Disc, ℂ)) :
    circleImage f = Set.range (fun θ : ℝ => f (circlePoint θ)) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, by simpa using congrArg f hθ⟩
  · rintro ⟨θ, rfl⟩
    refine ⟨circlePoint θ, ?_, rfl⟩
    show ‖(((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc)) : ℂ)‖ = 1
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-! ## The decomposition of the image and of the complement of the boundary -/

/-- **The image of an embedded disc is the union of the open image and the boundary circle.** -/
theorem range_eq_openImage_union_circleImage (f : C(Disc, ℂ)) :
    Set.range f = openImage f ∪ circleImage f := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hz1 : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    rcases lt_or_eq_of_le hz1 with hlt | heq
    · exact Or.inl ⟨z, hlt, rfl⟩
    · exact Or.inr ⟨z, heq, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨z, rfl⟩

/-- The open image and the boundary circle are disjoint. -/
theorem disjoint_openImage_circleImage {f : C(Disc, ℂ)} (hf : Function.Injective f) :
    Disjoint (openImage f) (circleImage f) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
  simp only [Set.mem_setOf_eq] at hz hz'
  have hzz : z = z' := hf hzz'.symm
  rw [← hzz] at hz'
  rw [hz'] at hz
  exact absurd hz (by norm_num)

/-- **The complement of the boundary circle is the disjoint union of the open image and the
complement of the image of the disc.** -/
theorem compl_circleImage_eq_openImage_union_compl {f : C(Disc, ℂ)}
    (hf : Function.Injective f) :
    (circleImage f)ᶜ = openImage f ∪ (Set.range f)ᶜ := by
  have hdisj := disjoint_openImage_circleImage hf
  ext x
  rw [Set.mem_compl_iff, Set.mem_union]
  constructor
  · intro hx
    by_cases hxf : x ∈ Set.range f
    · refine Or.inl ?_
      rw [range_eq_openImage_union_circleImage f] at hxf
      rcases hxf with h | h
      · exact h
      · exact absurd h hx
    · exact Or.inr hxf
  · rintro (hx | hx)
    · rintro ⟨z, hz, rfl⟩
      exact (Set.disjoint_left.mp hdisj) hx ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hx ⟨z, rfl⟩

/-! ## The reduction -/

/-- **The complement of an embedded disc is preconnected, from the "at most two components" half of
the Jordan curve theorem.** -/
theorem compl_range_preconnected_of_atMostTwo
    (h2 : ∀ (γ : ℝ → ℂ), Continuous γ → Function.Periodic γ (2 * Real.pi) →
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) →
      ∀ x y z : ℂ, x ∉ Set.range γ → y ∉ Set.range γ → z ∉ Set.range γ →
        connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
        connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
        connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z)
    {f : C(Disc, ℂ)} (hf : Function.Injective f) : IsPreconnected (Set.range f)ᶜ := by
  set γ : ℝ → ℂ := fun θ => f (circlePoint θ) with hγdef
  have hγcont : Continuous γ := f.continuous.comp hlp_continuous_circlePoint
  have hγper : Function.Periodic γ (2 * Real.pi) := fun θ => by
    show f (circlePoint (θ + 2 * Real.pi)) = f (circlePoint θ)
    rw [hlp_circlePoint_add_two_pi θ]
  have hγinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) := fun a ha b hb hab =>
    circlePoint_injOn_Ico_period ha hb (hf hab)
  have h2γ := h2 γ hγcont hγper hγinj
  -- the trace of the curve is the boundary circle image
  have hCrange : Set.range γ = circleImage f := (circleImage_eq_range_circlePoint f).symm
  -- the two pieces
  have hcompl : (Set.range γ)ᶜ = openImage f ∪ (Set.range f)ᶜ := by
    rw [hCrange]
    exact compl_circleImage_eq_openImage_union_compl hf
  have hOopen : IsOpen (openImage f) := openImage_isOpen hf
  have hEopen : IsOpen ((Set.range f)ᶜ) :=
    (isCompact_range f.continuous).isClosed.isOpen_compl
  have hOdisj : Disjoint (openImage f) ((Set.range f)ᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨z, hz, rfl⟩ hx'
    exact hx' ⟨z, rfl⟩
  have hxO : f 0 ∈ openImage f := ⟨0, by simp, rfl⟩
  -- the exterior of the disc is nonempty (it is bounded)
  obtain ⟨R, hR⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (f 0)) (hR _ ⟨0, rfl⟩)
  have hy₀ : ((R + 1 : ℝ) : ℂ) ∉ Set.range f := by
    intro hcon
    have h1 := hR _ hcon
    have h2 : ‖(((R + 1 : ℝ) : ℂ))‖ = R + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [h2] at h1
    exact absurd h1 (by linarith)
  -- a component of the complement of the curve meeting the exterior lies in the exterior
  have hkey : ∀ y : ℂ, y ∈ (Set.range f)ᶜ →
      connectedComponentIn (Set.range γ)ᶜ y ⊆ (Set.range f)ᶜ := by
    intro y hy
    have hyC : y ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inr hy
    have hsub : connectedComponentIn (Set.range γ)ᶜ y ⊆ (Set.range f)ᶜ ∪ openImage f := by
      intro z hz
      have h1 : z ∈ (Set.range γ)ᶜ := connectedComponentIn_subset (Set.range γ)ᶜ y hz
      rw [hcompl] at h1
      rcases h1 with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    exact IsPreconnected.subset_left_of_subset_union hEopen hOopen hOdisj.symm hsub
      ⟨y, mem_connectedComponentIn hyC, hy⟩ isPreconnected_connectedComponentIn
  -- two points of the exterior share their component of the complement of the curve
  have hsame : ∀ y z : ℂ, y ∈ (Set.range f)ᶜ → z ∈ (Set.range f)ᶜ →
      connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
    intro y z hy hz
    by_contra hne
    have hyC : y ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inr hy
    have hzC : z ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inr hz
    have hx0C : f 0 ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inl hxO
    have hxy : connectedComponentIn (Set.range γ)ᶜ (f 0) ≠ connectedComponentIn (Set.range γ)ᶜ y := by
      intro hcon
      have hmem : f 0 ∈ connectedComponentIn (Set.range γ)ᶜ y := by
        rw [← hcon]; exact mem_connectedComponentIn hx0C
      exact (hkey y hy hmem) ⟨0, rfl⟩
    have hxz : connectedComponentIn (Set.range γ)ᶜ (f 0) ≠ connectedComponentIn (Set.range γ)ᶜ z := by
      intro hcon
      have hmem : f 0 ∈ connectedComponentIn (Set.range γ)ᶜ z := by
        rw [← hcon]; exact mem_connectedComponentIn hx0C
      exact (hkey z hz hmem) ⟨0, rfl⟩
    have hsubrange : circleImage f ⊆ Set.range f := by
      rw [range_eq_openImage_union_circleImage]; exact Set.subset_union_right
    have hx0not : f 0 ∉ Set.range γ := by
      rw [hCrange]
      exact fun hcon => (Set.disjoint_left.mp (disjoint_openImage_circleImage hf)) hxO hcon
    have hyγ : y ∉ Set.range γ := by rw [hCrange]; exact fun hc => hy (hsubrange hc)
    have hzγ : z ∉ Set.range γ := by rw [hCrange]; exact fun hc => hz (hsubrange hc)
    rcases h2γ (f 0) y z hx0not hyγ hzγ with h | h | h
    · exact hxy h
    · exact hxz h
    · exact hne h
  -- conclude: the exterior is exactly a component of the complement of the curve
  have hset : (Set.range f)ᶜ = connectedComponentIn (Set.range γ)ᶜ (((R + 1 : ℝ) : ℂ)) := by
    apply Subset.antisymm
    · intro z hz
      rw [← hsame z _ hz hy₀]
      exact mem_connectedComponentIn (by rw [hcompl]; exact Or.inr hz)
    · exact hkey _ hy₀
  rw [hset]
  exact isPreconnected_connectedComponentIn

/-! ## The classical input, and the target -/

/-- **The "at most two components" half of the Jordan curve theorem for a continuous simple closed
plane curve** — the classical input of this file (delegated). -/
theorem jordan_compl_atMostTwo_aux {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x y z : ℂ} (hx : x ∉ Set.range γ) (hy : y ∉ Set.range γ) (hz : z ∉ Set.range γ) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
    connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z :=
  Work.Smooth.SphereJordan.jordan_compl_atMostTwo hcont hper hinj hx hy hz

theorem compl_range_disc_preconnected_plane {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) : IsPreconnected (Set.range f)ᶜ :=
  compl_range_preconnected_of_atMostTwo
    (fun γ hc hp hi x y z hx hy hz => jordan_compl_atMostTwo_aux hc hp hi hx hy hz) hf

end

end Work.Smooth.SphereJordan
