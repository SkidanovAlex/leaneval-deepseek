import Mathlib
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.ppParity.Shift
import Submission.Work.Drive.transportThreeLevel

/-!
# Smallness of the intrinsic shift: the level faces stay avoided

* `Work.Drive.exists_eps_ppShift_avoidances` — if the base pair-meet set `ppMeet E E' V W` avoids the
  two level faces `ftY2 ∈ {0,1}`, `ftZ2 ∈ {0,1}` (`havY`, `havZ`), then so do the meets of the
  intrinsically perturbed family
  `ppShift Ξ w (unpackFst τ) E`, `ppShift Ξ w (unpackSnd τ) E'`, for all parameters `τ` of
  sufficiently small norm.

The content is *compactness + continuity alone*: a bad meet of a small perturbation would accumulate,
inside the compact nine-box, at a bad meet of the base family (`hΞ0` says the perturbation is the
identity at `τ = 0`), which `havY`/`havZ` forbid.  The perturbation length enters only through the
joint continuity of `(τ, x) ↦ Ξ (w (ftS x) • unpackFst τ) (E (ftS x) (ftU x))`, which is
`hΞc ∘ ((τ,x) ↦ (w (ftS x) • unpackFst τ, E (ftS x) (ftU x)))`.
-/

namespace Work.Drive

/-- At the zero parameter, the intrinsic shift does not move the chain: the first block. -/
private lemma ppShift_unpackFst_zero {M : Type*}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} (hΞ0 : ∀ p : M, Ξ 0 p = p)
    {w : ℝ → ℝ} {E : ℝ → EuclideanSpace ℝ (Fin 2) → M} (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    ppShift Ξ w (unpackFst (0 : EuclideanSpace ℝ (Fin 8))) E s u = E s u := by
  simp only [ppShift, map_zero, smul_zero]
  exact hΞ0 _

/-- At the zero parameter, the intrinsic shift does not move the chain: the second block. -/
private lemma ppShift_unpackSnd_zero {M : Type*}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} (hΞ0 : ∀ p : M, Ξ 0 p = p)
    {w : ℝ → ℝ} {E : ℝ → EuclideanSpace ℝ (Fin 2) → M} (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    ppShift Ξ w (unpackSnd (0 : EuclideanSpace ℝ (Fin 8))) E s u = E s u := by
  simp only [ppShift, map_zero, smul_zero]
  exact hΞ0 _

/-- **Joint continuity of the perturbed first block**, in the parameter and the point. -/
private lemma continuous_ppShift_fst
    {M : Type*} [TopologicalSpace M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞc : Continuous (fun p : EuclideanSpace ℝ (Fin 4) × M => Ξ p.1 p.2))
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)))
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackFst q.1 :=
    (hw.comp (by unfold ftS; fun_prop)).smul (unpackFst.continuous.comp continuous_fst)
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E (ftS q.2) (ftU q.2) := hEc.comp continuous_snd
  have h3 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (w (ftS q.2) • unpackFst q.1, E (ftS q.2) (ftU q.2)) := h1.prodMk h2
  simpa only [ppShift, Function.comp_def] using hΞc.comp h3

/-- **Joint continuity of the perturbed second block**, in the parameter and the point. -/
private lemma continuous_ppShift_snd
    {M : Type*} [TopologicalSpace M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞc : Continuous (fun p : EuclideanSpace ℝ (Fin 4) × M => Ξ p.1 p.2))
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)))
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E (ftS q.2) (ftU q.2)) := by
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      w (ftS q.2) • unpackSnd q.1 :=
    (hw.comp (by unfold ftS; fun_prop)).smul (unpackSnd.continuous.comp continuous_fst)
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      E (ftS q.2) (ftU q.2) := hEc.comp continuous_snd
  have h3 : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      (w (ftS q.2) • unpackSnd q.1, E (ftS q.2) (ftU q.2)) := h1.prodMk h2
  simpa only [ppShift, Function.comp_def] using hΞc.comp h3

theorem exists_eps_ppShift_avoidances
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞc : Continuous (Function.uncurry Ξ))
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (w : ℝ → ℝ) (hwc : Continuous w)
    (hEc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E (Work.Drive.ftS x) (Work.Drive.ftU x))
    (hE'c : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E' (Work.Drive.ftS x) (Work.Drive.ftU x))
    (hVc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY x))
    (hWc : Continuous fun x : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ x))
    (havY : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Work.Drive.ppMeet E E' V W, Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε →
      ∀ x ∈ Work.Drive.ppMeet (ppShift Ξ w (Work.Drive.unpackFst τ) E)
        (ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W,
        Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1 ∧
          Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1 := by
  classical
  -- ### Joint continuity of the four blocks of the perturbed configuration
  have hAc : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) :=
    continuous_ppShift_fst (M := M) hΞc hEc hwc
  have hCc : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) :=
    continuous_ppShift_snd (M := M) hΞc hE'c hwc
  have hBc : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (ftY q.2) := hVc.comp continuous_snd
  have hDc : Continuous fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (ftZ q.2) := hWc.comp continuous_snd
  -- ### The set of forbidden level coordinates is closed
  set Bad : Set (EuclideanSpace ℝ (Fin 9)) :=
    {x | ¬(ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 ∧ ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)} with hBad
  have hBadClosed : IsClosed Bad := by
    rw [hBad]
    have hY2c : Continuous fun x : EuclideanSpace ℝ (Fin 9) => ftY2 x := by
      unfold ftY2; fun_prop
    have hZ2c : Continuous fun x : EuclideanSpace ℝ (Fin 9) => ftZ2 x := by
      unfold ftZ2; fun_prop
    have h1 : IsClosed {x : EuclideanSpace ℝ (Fin 9) | ftY2 x = (0 : ℝ)} :=
      isClosed_eq hY2c continuous_const
    have h2 : IsClosed {x : EuclideanSpace ℝ (Fin 9) | ftY2 x = (1 : ℝ)} :=
      isClosed_eq hY2c continuous_const
    have h3 : IsClosed {x : EuclideanSpace ℝ (Fin 9) | ftZ2 x = (0 : ℝ)} :=
      isClosed_eq hZ2c continuous_const
    have h4 : IsClosed {x : EuclideanSpace ℝ (Fin 9) | ftZ2 x = (1 : ℝ)} :=
      isClosed_eq hZ2c continuous_const
    have he : {x : EuclideanSpace ℝ (Fin 9) |
          ¬(ftY2 x ≠ 0 ∧ ftY2 x ≠ 1 ∧ ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1)}
        = {x : EuclideanSpace ℝ (Fin 9) | ftY2 x = 0} ∪ {x | ftY2 x = 1} ∪
          {x | ftZ2 x = 0} ∪ {x | ftZ2 x = 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      tauto
    rw [he]
    exact ((h1.union h2).union h3).union h4
  -- ### The closed set of bad meets with the parameter in the unit ball
  set T : Set (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) :=
    {p | ‖p.1‖ ≤ 1 ∧ p.2 ∈ Submission.Drive.unitBox 8 ∧
      ppShift Ξ w (unpackFst p.1) E (ftS p.2) (ftU p.2) = V (ftY p.2) ∧
      ppShift Ξ w (unpackSnd p.1) E' (ftS p.2) (ftU p.2) = W (ftZ p.2) ∧
      p.2 ∈ Bad} with hT
  have hTclosed : IsClosed T := by
    have h1 : IsClosed {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) | ‖p.1‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have h2 : IsClosed {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        p.2 ∈ Submission.Drive.unitBox 8} :=
      (isCompact_unitBox 8).isClosed.preimage continuous_snd
    have h3 : IsClosed {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst p.1) E (ftS p.2) (ftU p.2) = V (ftY p.2)} :=
      isClosed_eq hAc hBc
    have h4 : IsClosed {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackSnd p.1) E' (ftS p.2) (ftU p.2) = W (ftZ p.2)} :=
      isClosed_eq hCc hDc
    have h5 : IsClosed {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) | p.2 ∈ Bad} :=
      hBadClosed.preimage continuous_snd
    have he : T = {p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) | ‖p.1‖ ≤ 1} ∩
        {p | p.2 ∈ Submission.Drive.unitBox 8} ∩
        {p | ppShift Ξ w (unpackFst p.1) E (ftS p.2) (ftU p.2) = V (ftY p.2)} ∩
        {p | ppShift Ξ w (unpackSnd p.1) E' (ftS p.2) (ftU p.2) = W (ftZ p.2)} ∩
        {p | p.2 ∈ Bad} := by
      rw [hT]
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [he]
    exact (((h1.inter h2).inter h3).inter h4).inter h5
  have hTcomp : IsCompact T := by
    have hsub : T ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) 1 ×ˢ
        Submission.Drive.unitBox 8 := by
      intro p hp
      rw [hT] at hp
      exact ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hp.1, hp.2.1⟩
    exact (((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) 1).prod
      (isCompact_unitBox 8))).of_isClosed_subset hTclosed hsub
  -- ### The zero parameter is not the parameter of a bad meet
  have h0 : (0 : EuclideanSpace ℝ (Fin 8)) ∉ Prod.fst '' T := by
    rintro ⟨p, hp, hp1⟩
    rw [hT] at hp
    obtain ⟨-, hbox, hm1, hm2, hbad⟩ := hp
    have hY : E (ftS p.2) (ftU p.2) = V (ftY p.2) := by
      have h := hm1
      rw [hp1] at h
      rw [ppShift_unpackFst_zero hΞ0 (ftS p.2) (ftU p.2)] at h
      exact h
    have hZ : E' (ftS p.2) (ftU p.2) = W (ftZ p.2) := by
      have h := hm2
      rw [hp1] at h
      rw [ppShift_unpackSnd_zero hΞ0 (ftS p.2) (ftU p.2)] at h
      exact h
    have hmeet : p.2 ∈ ppMeet E E' V W := ⟨hbox, hY, hZ⟩
    obtain ⟨hy0, hy1⟩ := havY p.2 hmeet
    obtain ⟨hz0, hz1⟩ := havZ p.2 hmeet
    exact hbad ⟨hy0, hy1, hz0, hz1⟩
  -- ### Extract the uniform radius
  have hTfstClosed : IsClosed (Prod.fst '' T) := (hTcomp.image continuous_fst).isClosed
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    Metric.isOpen_iff.mp hTfstClosed.isOpen_compl (0 : EuclideanSpace ℝ (Fin 8)) h0
  refine ⟨min ε₀ 1, lt_min hε₀pos one_pos, ?_⟩
  intro τ hτ x hx
  by_contra hcon
  have hτ1 : ‖τ‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hτ (min_le_right ε₀ 1))
  have hxT : (τ, x) ∈ T := by
    rw [hT]
    exact ⟨hτ1, hx.1, hx.2.1, hx.2.2, hcon⟩
  have hthis : τ ∈ Prod.fst '' T := ⟨(τ, x), hxT, rfl⟩
  have hτball : τ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 8)) ε₀ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hτ (min_le_left ε₀ 1)
  exact hε₀ hτball hthis

end Work.Drive
