import Mathlib
import Submission.Work.Smooth.JordanSeparation.plWalk
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx
import Submission.Work.Smooth.JordanSeparation.plApprox

/-!
# The polygonal approximation of a loop in an open set (step (A))

A loop `γ` in an open `U ⊆ ℂ` is homotopic *in* `↥U` to a polygonal loop through points of its
trace: the unit interval is partitioned (Lebesgue number for the open cover `γ ⁻¹' ball (γ s) δ`),
each restriction of `γ` to a subinterval is compared — inside `↥U`, by `homotopic_of_convex_subset`
— with the corresponding chord (both lie in one convex ball contained in `U`), and the pieces are
glued with `joinNat_congr` after `homotopic_restr_joinNat`.

The convex witnesses `B` are carried inside the existential, so that the conclusion (the homotopy
to the lifted join of the chords) can refer to them.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- The open ball of `ℂ`, as a `Set ℂ` (avoids the metric-space ambiguity of `ball`). -/
def cball (z : ℂ) (r : ℝ) : Set ℂ := Metric.ball z r

theorem convex_cball (z : ℂ) (r : ℝ) : Convex ℝ (cball z r) := convex_ball z r

theorem isOpen_cball (z : ℂ) (r : ℝ) : IsOpen (cball z r) := isOpen_ball

theorem mem_cball_self {z : ℂ} {r : ℝ} (h : 0 < r) : z ∈ cball z r := mem_ball_self h

/-- The affine reparametrisation `affine 0 1` is the identity. -/
theorem affine_zero_one (s : unitInterval) : Path.affine 0 1 s = s := by
  ext
  rw [Path.affine_val']
  push_cast
  ring

/-- A loop is its own restriction to the full unit interval, up to the endpoint casts. -/
theorem cast_restr_zero_one {U : Set ℂ} {x : ℂ} (hx : x ∈ U)
    (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    Path.cast (γ.restr 0 1) γ.source.symm γ.target.symm = γ := by
  ext s
  rw [Path.cast_coe, Path.restr_apply, affine_zero_one]

/-- **Polygonal approximation.**  A loop `γ` in an open `U ⊆ ℂ` is homotopic in `↥U` to the join of
the chords of a finite partition of its trace, each chord being lifted to `↥U` through a convex
witness `B k ⊆ U` containing the corresponding piece of the loop. -/
theorem exists_polygonal_homotopic {U : Set ℂ} (hUo : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    ∃ (N : ℕ) (t : ℕ → unitInterval) (B : ℕ → Set ℂ)
      (h0 : t 0 = 0) (hN : t N = 1) (hmono : Monotone t)
      (hconv : ∀ k < N, Convex ℝ (B k))
      (hBU : ∀ k < N, B k ⊆ U)
      (hval : ∀ k < N, ∀ s : unitInterval, s ∈ Set.Icc (t k) (t (k + 1)) → (γ s : ℂ) ∈ B k),
      Path.Homotopic γ (Path.cast (joinNat (p := fun i => γ (t i))
        (fun k => if hk : k < N then
            Path.liftU (γ (t k)).2 (γ (t (k + 1))).2
              (segPath ((γ (t k) : ℂ)) ((γ (t (k + 1)) : ℂ)))
              (fun s => hBU k hk (Convex.segment_subset (hconv k hk)
                (hval k hk (t k) ⟨le_refl _, hmono (Nat.le_succ k)⟩)
                (hval k hk (t (k + 1)) ⟨hmono (Nat.le_succ k), le_refl _⟩)
                (segPath_mem_segment _ _ _ ⟨s, rfl⟩)))
          else γ.restr (t k) (t (k + 1))) N)
        (γ.source.symm.trans (congrArg γ h0.symm))
        (γ.target.symm.trans (congrArg γ hN.symm))) := by
  have hball : ∀ s : unitInterval, ∃ δ : ℝ, 0 < δ ∧ cball ((γ s : ℂ)) δ ⊆ U := by
    intro s
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds (γ s).2)
    exact ⟨δ, hδ, hsub⟩
  choose δ hδpos hδsub using hball
  have hcov : (univ : Set unitInterval) ⊆ ⋃ s : unitInterval,
      ((fun u : unitInterval => (γ u : ℂ)) ⁻¹' cball ((γ s : ℂ)) (δ s)) := by
    intro u _
    exact mem_iUnion.mpr ⟨u, mem_cball_self (hδpos u)⟩
  have hopen : ∀ s : unitInterval,
      IsOpen ((fun u : unitInterval => (γ u : ℂ)) ⁻¹' cball ((γ s : ℂ)) (δ s)) :=
    fun s => (isOpen_cball ((γ s : ℂ)) (δ s)).preimage (continuous_subtype_val.comp γ.continuous)
  obtain ⟨t, ht0, htmono, ⟨n, hn⟩, hspec⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcov
  set θ : ℕ → unitInterval := fun k => Classical.choose (hspec k) with hθdef
  have hθ : ∀ k, Set.Icc (t k) (t (k + 1)) ⊆
      ((fun u : unitInterval => (γ u : ℂ)) ⁻¹' cball ((γ (θ k) : ℂ)) (δ (θ k))) :=
    fun k => Classical.choose_spec (hspec k)
  -- the convex witnesses
  have hconv' : ∀ k < n, Convex ℝ (if hk : k < n then cball ((γ (θ k) : ℂ)) (δ (θ k)) else univ) := by
    intro k hk
    rw [dif_pos hk]
    exact convex_cball _ _
  have hBU' : ∀ k < n,
      (if hk : k < n then cball ((γ (θ k) : ℂ)) (δ (θ k)) else univ) ⊆ U := by
    intro k hk
    rw [dif_pos hk]
    exact hδsub (θ k)
  have hval' : ∀ k < n, ∀ s : unitInterval, s ∈ Set.Icc (t k) (t (k + 1)) →
      (γ s : ℂ) ∈ (if hk : k < n then cball ((γ (θ k) : ℂ)) (δ (θ k)) else univ) := by
    intro k hk s hs
    rw [dif_pos hk]
    exact hθ k hs
  have hvalC : ∀ k, k < n → ∀ s : unitInterval, s ∈ Set.Icc (t k) (t (k + 1)) →
      (γ s : ℂ) ∈ cball ((γ (θ k) : ℂ)) (δ (θ k)) := by
    intro k hk s hs
    have h := hval' k hk s hs
    rw [dif_pos hk] at h
    exact h
  -- the chord family
  let hchord : ∀ k, Path (γ (t k)) (γ (t (k + 1))) := fun k =>
    if hk : k < n then
      Path.liftU (γ (t k)).2 (γ (t (k + 1))).2
        (segPath ((γ (t k) : ℂ)) ((γ (t (k + 1)) : ℂ)))
        (fun s => hBU' k hk (Convex.segment_subset (hconv' k hk)
          (hval' k hk (t k) ⟨le_refl _, htmono (Nat.le_succ k)⟩)
          (hval' k hk (t (k + 1)) ⟨htmono (Nat.le_succ k), le_refl _⟩)
          (segPath_mem_segment _ _ _ ⟨s, rfl⟩)))
    else γ.restr (t k) (t (k + 1))
  -- the endpoint casts
  have e1 : (⟨x, hx⟩ : ↥U) = γ (t 0) := γ.source.symm.trans (congrArg γ ht0.symm)
  have e2 : (⟨x, hx⟩ : ↥U) = γ (t n) := γ.target.symm.trans (congrArg γ (hn n le_rfl).symm)
  -- step 1
  have step1 : Path.Homotopic γ (Path.cast (γ.restr (t 0) (t n)) e1 e2) := by
    have heq : Path.cast (γ.restr (t 0) (t n)) e1 e2 = γ := by
      ext s
      rw [Path.cast_coe, Path.restr_apply, ht0, hn n le_rfl, affine_zero_one]
    rw [heq]
  -- step 2
  have step2 : Path.Homotopic (Path.cast (γ.restr (t 0) (t n)) e1 e2)
      (Path.cast (joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) n)
        e1 e2) :=
    Path.Homotopic.pathCast (homotopic_restr_joinNat γ t n) e1 e2
  -- step 3
  have step3 : ∀ k, Path.Homotopic (γ.restr (t k) (t (k + 1))) (hchord k) := by
    intro k
    by_cases hk : k < n
    · simp only [hchord, dif_pos hk]
      refine homotopic_of_convex_subset (U := U)
        (B := cball ((γ (θ k) : ℂ)) (δ (θ k))) (convex_cball _ _)
        ⟨(γ (t k) : ℂ), hvalC k hk (t k) ⟨le_refl _, htmono (Nat.le_succ k)⟩⟩
        (hδsub (θ k)) (γ.restr (t k) (t (k + 1)))
        (Path.liftU (γ (t k)).2 (γ (t (k + 1))).2
          (segPath ((γ (t k) : ℂ)) ((γ (t (k + 1)) : ℂ)))
          (fun s => hBU' k hk (Convex.segment_subset (hconv' k hk)
            (hval' k hk (t k) ⟨le_refl _, htmono (Nat.le_succ k)⟩)
            (hval' k hk (t (k + 1)) ⟨htmono (Nat.le_succ k), le_refl _⟩)
            (segPath_mem_segment _ _ _ ⟨s, rfl⟩))))
        (fun s => Path.restr_mem γ (htmono (Nat.le_succ k))
          (S := Subtype.val ⁻¹' cball ((γ (θ k) : ℂ)) (δ (θ k)))
          (fun u hu => hθ k hu) s)
        (fun s => Convex.segment_subset (convex_cball ((γ (θ k) : ℂ)) (δ (θ k)))
          (hvalC k hk (t k) ⟨le_refl _, htmono (Nat.le_succ k)⟩)
          (hvalC k hk (t (k + 1)) ⟨htmono (Nat.le_succ k), le_refl _⟩)
          (segPath_mem_segment _ _ _ ⟨s, rfl⟩))
    · simp only [hchord, dif_neg hk]
      exact Path.Homotopic.refl _
  -- glue
  have hjoin : Path.Homotopic
      (joinNat (p := fun i => γ (t i)) (fun k => γ.restr (t k) (t (k + 1))) n)
      (joinNat (p := fun i => γ (t i)) hchord n) :=
    joinNat_congr (p := fun i => γ (t i)) step3 n
  exact ⟨n, t, fun k => if hk : k < n then cball ((γ (θ k) : ℂ)) (δ (θ k)) else univ,
    ht0, hn n le_rfl, htmono, hconv', hBU', hval',
    step1.trans (step2.trans (Path.Homotopic.pathCast hjoin e1 e2))⟩

end

end Work.Smooth.JordanSeparation
