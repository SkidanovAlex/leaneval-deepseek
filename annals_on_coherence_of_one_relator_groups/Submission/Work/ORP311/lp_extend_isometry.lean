import Mathlib

/-!
# Extending `ℓ²` along an injection by zero

For an injective map `e : α → β`, the map "send `f` to the function on `β` which agrees with `f`
on `e '' α` and vanishes elsewhere" is a linear isometry `ℓ²(α, ℂ) →ₗᵢ[ℂ] ℓ²(β, ℂ)`.

The construction goes through the Hilbert-sum description of `ℓ²` (`lp.instInnerProductSpace`):
the coordinate `a` of the source embeds isometrically into the target as
`lp.single 2 (e a)` (`Work.ORP311.lpEmbedSingle`), and injectivity of `e` makes these images
pairwise orthogonal (`Work.ORP311.lpEmbedSingle_orthogonal`).  The associated
`OrthogonalFamily.linearIsometry` is the desired map (`Work.ORP311.lpExtendLie`); the pointwise
descriptions of its values (and its surjectivity onto the functions supported in `Set.range e`)
are then read off from `OrthogonalFamily.hasSum_linearIsometry` by applying the continuous
evaluation functional `lp.evalCLM`.
-/

open scoped lp

namespace Work.ORP311

/-- The isometric embedding of the `a`-th coordinate of `ℓ²(α, ℂ)` into `ℓ²(β, ℂ)`, sending
`c` to `lp.single 2 (e a) c`. -/
noncomputable def lpEmbedSingle {α β : Type*} [DecidableEq β] (e : α → β) (a : α) :
    ℂ →ₗᵢ[ℂ] lp (fun _ : β => ℂ) 2 :=
  LinearIsometry.mk (lp.lsingle (𝕜 := ℂ) (E := fun _ : β => ℂ) 2 (e a)) (fun c => by
    exact lp.norm_single (E := fun _ : β => ℂ) (p := 2) (by norm_num) (e a) c)

theorem lpEmbedSingle_apply {α β : Type*} [DecidableEq β] (e : α → β) (a : α) (c : ℂ) :
    lpEmbedSingle e a c = lp.single (E := fun _ : β => ℂ) 2 (e a) c := rfl

/-- The coordinate embeddings `lpEmbedSingle e a` have pairwise orthogonal ranges when `e` is
injective. -/
theorem lpEmbedSingle_orthogonal {α β : Type*} [DecidableEq β] {e : α → β}
    (he : Function.Injective e) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (lpEmbedSingle (β := β) e) := by
  intro a a' haa' c c'
  rw [lpEmbedSingle_apply, lpEmbedSingle_apply, lp.inner_single_left]
  have h : (lp.single (E := fun _ : β => ℂ) 2 (e a') c') (e a) = 0 := by
    rw [lp.single_apply, Pi.single_apply, if_neg]
    exact fun h => haa' (he h)
  rw [h, inner_zero_right]

/-- The evaluation functional is just "take the `b`-th coordinate". -/
theorem lp_evalCLM_apply {β : Type*} [DecidableEq β] (b : β) (x : lp (fun _ : β => ℂ) 2) :
    lp.evalCLM ℂ (fun _ : β => ℂ) 2 b x = (x : β → ℂ) b := by
  rw [show (⇑(lp.evalCLM ℂ (fun _ : β => ℂ) 2 b)) x
      = (lp.evalₗ (fun _ : β => ℂ) 2 b) x from rfl]
  rw [lp.evalₗ_apply]

theorem evalCLM_lpEmbedSingle {α β : Type*} [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : Function.Injective e) (i a : α) (c : ℂ) :
    lp.evalCLM ℂ (fun _ : β => ℂ) 2 (e a) (lpEmbedSingle e i c)
      = if i = a then c else 0 := by
  rw [lp_evalCLM_apply, lpEmbedSingle_apply, lp.single_apply, Pi.single_apply]
  by_cases h : i = a
  · subst h; simp
  · rw [if_neg h, if_neg (fun hh => h (he hh).symm)]

theorem evalCLM_lpEmbedSingle_of_notMem {α β : Type*} [DecidableEq β] {e : α → β}
    {b : β} (hb : b ∉ Set.range e) (i : α) (c : ℂ) :
    lp.evalCLM ℂ (fun _ : β => ℂ) 2 b (lpEmbedSingle e i c) = 0 := by
  rw [lp_evalCLM_apply, lpEmbedSingle_apply, lp.single_apply, Pi.single_apply]
  rw [if_neg]
  intro hh
  exact hb ⟨i, hh.symm⟩

/-- The "extend by zero along `e`" linear isometry `ℓ²(α, ℂ) →ₗᵢ[ℂ] ℓ²(β, ℂ)`. -/
noncomputable def lpExtendLie {α β : Type*} [DecidableEq β] (e : α → β)
    (he : Function.Injective e) :
    lp (fun _ : α => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : β => ℂ) 2 :=
  (lpEmbedSingle_orthogonal (β := β) he).linearIsometry

theorem lpExtendLie_single {α β : Type*} [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : Function.Injective e) (a : α) (c : ℂ) :
    lpExtendLie e he (lp.single (E := fun _ : α => ℂ) 2 a c)
      = lp.single (E := fun _ : β => ℂ) 2 (e a) c := by
  rw [lpExtendLie,
    OrthogonalFamily.linearIsometry_apply_single (lpEmbedSingle_orthogonal (β := β) he),
    lpEmbedSingle_apply]

/-- The extended function agrees with `f` on `e '' α`. -/
theorem lpExtendLie_apply_e {α β : Type*} [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : Function.Injective e) (f : lp (fun _ : α => ℂ) 2) (a : α) :
    (lpExtendLie e he f : β → ℂ) (e a) = (f : α → ℂ) a := by
  have hsum := (lpEmbedSingle_orthogonal (β := β) he).hasSum_linearIsometry f
  have hmap := hsum.map (lp.evalCLM ℂ (fun _ : β => ℂ) 2 (e a))
      (lp.evalCLM ℂ (fun _ : β => ℂ) 2 (e a)).continuous
  have h1 : lp.evalCLM ℂ (fun _ : β => ℂ) 2 (e a) (lpExtendLie e he f)
      = ∑' i : α, lp.evalCLM ℂ (fun _ : β => ℂ) 2 (e a) (lpEmbedSingle e i (f i)) := by
    rw [lpExtendLie]; exact hmap.tsum_eq.symm
  rw [← lp_evalCLM_apply, h1]
  trans ∑' i : α, (if i = a then (f : α → ℂ) i else 0)
  · congr 1 with i
    rw [evalCLM_lpEmbedSingle he i a (f i)]
  · rw [tsum_ite_eq]

/-- The extended function vanishes off `e '' α`. -/
theorem lpExtendLie_apply_notMem {α β : Type*} [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : Function.Injective e) (f : lp (fun _ : α => ℂ) 2) {b : β} (hb : b ∉ Set.range e) :
    (lpExtendLie e he f : β → ℂ) b = 0 := by
  have hsum := (lpEmbedSingle_orthogonal (β := β) he).hasSum_linearIsometry f
  have hmap := hsum.map (lp.evalCLM ℂ (fun _ : β => ℂ) 2 b)
      (lp.evalCLM ℂ (fun _ : β => ℂ) 2 b).continuous
  have h1 : lp.evalCLM ℂ (fun _ : β => ℂ) 2 b (lpExtendLie e he f)
      = ∑' i : α, lp.evalCLM ℂ (fun _ : β => ℂ) 2 b (lpEmbedSingle e i (f i)) := by
    rw [lpExtendLie]; exact hmap.tsum_eq.symm
  rw [← lp_evalCLM_apply, h1]
  simp only [evalCLM_lpEmbedSingle_of_notMem hb]
  exact tsum_zero

/-- Every element of `ℓ²(β, ℂ)` supported in `e '' α` is in the range of the extension map. -/
theorem lpExtendLie_surj {α β : Type*} [DecidableEq α] [DecidableEq β] {e : α → β}
    (he : Function.Injective e) (u : lp (fun _ : β => ℂ) 2)
    (hu : ∀ b : β, b ∉ Set.range e → (u : β → ℂ) b = 0) :
    ∃ w : lp (fun _ : α => ℂ) 2, lpExtendLie e he w = u := by
  refine ⟨⟨fun a => (u : β → ℂ) (e a), ?_⟩, ?_⟩
  · exact memℓp_gen (((lp.memℓp u).summable (p := 2) (by norm_num)).comp_injective he)
  · apply lp.ext
    funext b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      rw [lpExtendLie_apply_e he]
    · rw [lpExtendLie_apply_notMem he _ hb, hu b hb]

theorem lp_extend_isometry {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α → β)
    (he : Function.Injective e) :
    ∃ T : lp (fun _ : α => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : β => ℂ) 2,
      (∀ (a : α) (c : ℂ), T (lp.single 2 a c) = lp.single 2 (e a) c) ∧
      (∀ (f : lp (fun _ : α => ℂ) 2) (a : α), (T f : β → ℂ) (e a) = (f : α → ℂ) a) ∧
      (∀ (f : lp (fun _ : α => ℂ) 2) (b : β), b ∉ Set.range e → (T f : β → ℂ) b = 0) ∧
      (∀ u : lp (fun _ : β => ℂ) 2, (∀ b : β, b ∉ Set.range e → (u : β → ℂ) b = 0) →
        ∃ w : lp (fun _ : α => ℂ) 2, T w = u) := by
  refine ⟨lpExtendLie e he, ?_, ?_, ?_, ?_⟩
  · intro a c
    exact lpExtendLie_single he a c
  · intro f a
    exact lpExtendLie_apply_e he f a
  · intro f b hb
    exact lpExtendLie_apply_notMem he f hb
  · intro u hu
    exact lpExtendLie_surj he u hu

end Work.ORP311
