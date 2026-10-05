import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_jordan_arcs
import Submission.Work.RPB1a.Caratheodory.Maehara.circle_two_arcs

namespace Work.RPB.B1a.Maehara

/-- Two distinct points `a`, `b` on a Jordan curve `γ : Circle → ℝ × ℝ` split the curve into two
arcs, each running from `a` to `b`, injective on `[-1,1]`, together covering `range γ` and meeting
exactly in the two endpoints.

The work is done by `Work.RPB1a.Caratheodory.Maehara.circle_two_arcs`, which produces the two arcs
on the abstract circle parametrised by `[0,1]`; here we merely transport the parametrisation to
`[-1,1]` (via `t ↦ (t+1)/2`) and take the preimages of `a` and `b` under the injective `γ`. -/
theorem jordan_arcs_prod (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    {a b : ℝ × ℝ} (ha : a ∈ Set.range γ) (hb : b ∈ Set.range γ) (hab : a ≠ b) :
    ∃ P Q : ℝ → ℝ × ℝ, Continuous P ∧ Continuous Q ∧
      P (-1) = a ∧ P 1 = b ∧ Q (-1) = a ∧ Q 1 = b ∧
      Set.InjOn P (Set.Icc (-1 : ℝ) 1) ∧ Set.InjOn Q (Set.Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, P t ∈ Set.range γ) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, Q t ∈ Set.range γ) ∧
      Set.range γ = P '' Set.Icc (-1 : ℝ) 1 ∪ Q '' Set.Icc (-1 : ℝ) 1 ∧
      P '' Set.Icc (-1 : ℝ) 1 ∩ Q '' Set.Icc (-1 : ℝ) 1 = {a, b} := by
  -- Preimages of the two points in the circle.
  obtain ⟨za, hza⟩ := ha
  obtain ⟨zb, hzb⟩ := hb
  have hne : za ≠ zb := by
    intro h
    exact hab (by rw [← hza, ← hzb, h])
  -- The two arcs of the circle between `za` and `zb`, parametrised by `[0,1]`.
  obtain ⟨pc, pd, hpc, hpd, hpc0, hpc1, hpd0, hpd1, hpc_inj, hpd_inj, hunion, hinter⟩ :=
    Work.RPB1a.Caratheodory.Maehara.circle_two_arcs γ hγ hinj hne
  -- The affine reparametrisation `[0,1] → [-1,1]`, `s ↦ (s+1)/2`.
  have hg_mem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hPimg : (fun t : ℝ => pc ((t + 1) / 2)) '' Set.Icc (-1 : ℝ) 1
      = pc '' Set.Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t + 1) / 2, hg_mem t ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨2 * s - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      show pc (((2 * s - 1) + 1) / 2) = pc s
      rw [show ((2 * s - 1) + 1) / 2 = s by ring]
  have hQimg : (fun t : ℝ => pd ((t + 1) / 2)) '' Set.Icc (-1 : ℝ) 1
      = pd '' Set.Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t + 1) / 2, hg_mem t ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨2 * s - 1, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      show pd (((2 * s - 1) + 1) / 2) = pd s
      rw [show ((2 * s - 1) + 1) / 2 = s by ring]
  refine ⟨fun t => pc ((t + 1) / 2), fun t => pd ((t + 1) / 2),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `P` is continuous.
    exact hpc.comp (by fun_prop)
  · -- `Q` is continuous.
    exact hpd.comp (by fun_prop)
  · -- `P (-1) = a`.
    show pc (((-1 : ℝ) + 1) / 2) = a
    rw [show ((-1 : ℝ) + 1) / 2 = 0 by norm_num, hpc0, hza]
  · -- `P 1 = b`.
    show pc (((1 : ℝ) + 1) / 2) = b
    rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, hpc1, hzb]
  · -- `Q (-1) = a`.
    show pd (((-1 : ℝ) + 1) / 2) = a
    rw [show ((-1 : ℝ) + 1) / 2 = 0 by norm_num, hpd0, hza]
  · -- `Q 1 = b`.
    show pd (((1 : ℝ) + 1) / 2) = b
    rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, hpd1, hzb]
  · -- `P` is injective on `[-1,1]`.
    intro t ht t' ht' h
    have hpar := hpc_inj ((t + 1) / 2) (hg_mem t ht) ((t' + 1) / 2) (hg_mem t' ht') h
    linarith
  · -- `Q` is injective on `[-1,1]`.
    intro t ht t' ht' h
    have hpar := hpd_inj ((t + 1) / 2) (hg_mem t ht) ((t' + 1) / 2) (hg_mem t' ht') h
    linarith
  · -- Every value of `P` lies on the curve.
    intro t ht
    have hmem : pc ((t + 1) / 2) ∈ pc '' Set.Icc (0 : ℝ) 1 :=
      ⟨(t + 1) / 2, hg_mem t ht, rfl⟩
    have hmem' : pc ((t + 1) / 2)
        ∈ pc '' Set.Icc (0 : ℝ) 1 ∪ pd '' Set.Icc (0 : ℝ) 1 := Or.inl hmem
    rwa [hunion] at hmem'
  · -- Every value of `Q` lies on the curve.
    intro t ht
    have hmem : pd ((t + 1) / 2) ∈ pd '' Set.Icc (0 : ℝ) 1 :=
      ⟨(t + 1) / 2, hg_mem t ht, rfl⟩
    have hmem' : pd ((t + 1) / 2)
        ∈ pc '' Set.Icc (0 : ℝ) 1 ∪ pd '' Set.Icc (0 : ℝ) 1 := Or.inr hmem
    rwa [hunion] at hmem'
  · -- The two arcs cover the whole curve.
    rw [hPimg, hQimg]
    exact hunion.symm
  · -- The two arcs meet exactly in the two endpoints.
    rw [hPimg, hQimg, hinter, hza, hzb]

end Work.RPB.B1a.Maehara
