import Mathlib
import Submission.Work.Drive.PushDisc.lensAssemblyThinSolid

/-!
# `lensAssemblyThinWired`: the thin assembly with the disc's top-edge row restricted to the window

This is a copy of the **proved** `Work.Drive.PushDisc.lensAssemblyThinSolid` (the thin-tube
assembly of the compact `n ≥ 3` case) with exactly one edit: the row

  `hΔ1 : ∀ x, Δ (x, arch x) = Φ₀ (f (c₂.symm (splitE k (x, 0))))`

is restricted to `|x| ≤ X'`.  The restriction is necessary for the *consumer*: `c₂.symm` is an
`OpenPartialHomeomorph.invFun`, i.e. arbitrary off `c₂.target`, and the target of the chart produced
by `exists_chart_of_arc` only contains a tube of *some* radius around the straightened arc (the row
`hwinc` of the assembly), so the unrestricted identity is not satisfiable.  The assembly's own proof
uses `hΔ1` only at a point with `|p.1| < 1` (`habs1`), hence the restriction is harmless.

Only the proof and the statement of the assembly are repeated here; everything else (the finger
block rows, the isolation `exists_isolation_of_cleanRegion`, the model disc) is imported from the
proved modules.

-/

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold Topology
open Set Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

/-! ## The thin assembly, with the top-edge row restricted to the window -/

theorem lensAssemblyThinWired {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X') (r : ℝ) (hr : 0 < r)
    (ε : ℝ) (hε : 0 < ε)
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγ₂W : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (Φ₀ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ₀ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₀)
    (hΘ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ₀)
    (hΘ₀Φ₀ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ₀ (Φ₀ y) = y)
    (hΦ₀Θ₀ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ₀ (Θ₀ ξ) = ξ)
    (U₁ : Set M) (hU₁o : IsOpen U₁) (hU₁W : U₁ ⊆ W)
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ₀ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hseg : ∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ₀ (f z) = (x, 0, 0, 0))
    (hp₁c : f p₁ = Θ₀ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ₀ ((1 : ℝ), 0, 0, 0))
    (hpin₂ : Φ₀ (f p₂) = ((-1 : ℝ), 0, 0, 0)) (hpin₄ : Φ₀ (f q₂) = ((1 : ℝ), 0, 0, 0))
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂W : c₂.source ⊆ W)
    (hp₂c₂ : p₂ ∈ c₂.source) (hq₂c₂ : q₂ ∈ c₂.source)
    (harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c₂ (γ₂ t) = Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k))))
    (hwinc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ Work.Drive.PushDisc.asymReg k X' →
      Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target)
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hΔsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hΔ0 : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hΔ1 : ∀ x : ℝ, |x| ≤ X' → Δ (x, Work.Drive.PushDisc.arch x)
      = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
    (hΔclean : ∀ z : M, Φ₀ (f z) ∉ Δ '' Work.Drive.PushDisc.lensKo)
    (Θg Θgi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (hΘgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θg)
    (hΘgism : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θgi)
    (hlΘ : Function.LeftInverse Θgi Θg) (hrΘ : Function.RightInverse Θgi Θg)
    (hplane0 : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X' → ‖u‖ ≤ ε →
      Θg (x, 0, u, (0 : EuclideanSpace ℝ (Fin k))) = (x, 0, u, (0 : EuclideanSpace ℝ (Fin k))))
    (hdisc : ∀ (x y : ℝ), |x| ≤ X' → 0 ≤ y → y ≤ Work.Drive.PushDisc.arch x →
      Θg (x, y, 0, 0) = Δ (x, y))
    (hfinger : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Θg (x, Work.Drive.PushDisc.arch x, 0, w)
        = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w)))))
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    Nonempty (Work.Drive.PushDisc.ChartObligation n f W p₁ p₂ q₁ q₂) := by
  subst hk
  -- ### the chart pair `(Φ, Θ) = (Θgi ∘ Φ₀, Θ₀ ∘ Θg)`
  set Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k :=
    fun y => Θgi (Φ₀ y) with hΦdef
  set Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    fun ξ => Θ₀ (Θg ξ) with hΘdef
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := hΘgism.comp hΦ₀sm
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := hΘ₀sm.comp hΘgsm
  have hΘΦ : ∀ y, Θ (Φ y) = y := by
    intro y
    change Θ₀ (Θg (Θgi (Φ₀ y))) = y
    rw [hrΘ (Φ₀ y), hΘ₀Φ₀ y]
  have hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ := by
    intro ξ
    change Θgi (Φ₀ (Θ₀ (Θg ξ))) = ξ
    rw [hΦ₀Θ₀ (Θg ξ), hlΘ ξ]
  have hΦ₀inj : Function.Injective Φ₀ := fun a b h => by
    have h2 := congrArg Θ₀ h
    rwa [hΘ₀Φ₀ a, hΘ₀Φ₀ b] at h2
  have hΘg_neg : Θg ((-1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
      (0 : EuclideanSpace ℝ (Fin k)))
      = ((-1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) :=
    hplane0 (-1) 0 (by simp only [abs_neg, abs_one]; linarith [hX']) (by simpa using hε.le)
  have hΘg_pos : Θg ((1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
      (0 : EuclideanSpace ℝ (Fin k)))
      = ((1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) :=
    hplane0 1 0 (by simp only [abs_one]; linarith [hX']) (by simpa using hε.le)
  -- ### the finger row, in `Φ`-coordinates
  have hfingerΦ : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w))))
        = (x, Work.Drive.PushDisc.arch x, 0, w) := by
    intro x w hx hw
    change Θgi (Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w)))))
      = (x, Work.Drive.PushDisc.arch x, 0, w)
    rw [← hfinger x w hx hw]
    exact hlΘ _
  -- ### the finger block
  obtain ⟨hh, hσ₂row, hp₂f, hq₂f, hW₀o, hW₀W, hcore, hlip, hfrontier⟩ :=
    fingerBlockRows f hf Φ Θ hΦsm hΘsm hΘΦ hΦΘ W p₂ q₂ γ₂ hγ₂ hγ₂0 hγ₂1 hγ₂W c₂ hc₂W hp₂c₂
      hq₂c₂ harc₂ X' hX' r hr hwinc hfingerΦ
  have hσ₂inj : Set.InjOn (fingerParam c₂ r) (Work.Drive.PushDisc.asymReg k X') :=
    fingerParam_injOn c₂ hr hwinc
  -- ### the two pins are not in the flat tube
  have hmem_neg : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈
      Work.Drive.PushDisc.asymReg k X' := by
    refine ⟨?_, by simp⟩
    simp only [abs_neg, abs_one]; linarith [hX']
  have hmem_pos : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈
      Work.Drive.PushDisc.asymReg k X' := by
    refine ⟨?_, by simp⟩
    simp only [abs_one]; linarith [hX']
  have hcont_neg : ContinuousAt (fingerParam c₂ r) ((-1 : ℝ), 0) := by
    have hinner : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) ((-1 : ℝ), 0) :=
      (continuous_splitReg k r).continuousAt
    have hmemT : Work.Drive.PushDisc.splitE k ((-1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))
        ∈ c₂.target := hwinc _ hmem_neg
    change ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
      c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • p.2))) ((-1 : ℝ), 0)
    exact ContinuousAt.comp (g := c₂.symm)
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) (c₂.continuousAt_symm hmemT) hinner
  have hcont_pos : ContinuousAt (fingerParam c₂ r) ((1 : ℝ), 0) := by
    have hinner : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) ((1 : ℝ), 0) :=
      (continuous_splitReg k r).continuousAt
    have hmemT : Work.Drive.PushDisc.splitE k ((1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))
        ∈ c₂.target := hwinc _ hmem_pos
    change ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
      c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • p.2))) ((1 : ℝ), 0)
    exact ContinuousAt.comp (g := c₂.symm)
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) (c₂.continuousAt_symm hmemT) hinner
  have hp₂U₀ : fingerParam c₂ r ((-1 : ℝ), 0) ∉ U₁ :=
    not_mem_U₁_of_finger_pin_thin (f := f) hU₁o hlΘ hΘgsm.continuous hX' hε hplane0 hU₁row
      (fun x w hx hw => hfinger x w hx hw) (Or.inl rfl) hcont_neg
  have hq₂U₀ : fingerParam c₂ r ((1 : ℝ), 0) ∉ U₁ :=
    not_mem_U₁_of_finger_pin_thin (f := f) hU₁o hlΘ hΘgsm.continuous hX' hε hplane0 hU₁row
      (fun x w hx hw => hfinger x w hx hw) (Or.inr rfl) hcont_pos
  -- ### the tube is cut down to the part of the plane on which `Θg` is the identity
  have hΦ₀fc : Continuous (fun x : M => Φ₀ (f x)) := hΦ₀sm.continuous.comp hf.continuous
  set U₁' : Set M := U₁ ∩ {x : M | |(Φ₀ (f x)).1| < X'}
      ∩ {x : M | ‖(Φ₀ (f x)).2.2.1‖ < ε} with hU₁'def
  have hU₁'o : IsOpen U₁' := by
    have h1 : IsOpen {x : M | |(Φ₀ (f x)).1| < X'} :=
      isOpen_lt (continuous_abs.comp (continuous_fst.comp hΦ₀fc)) continuous_const
    have h2 : IsOpen {x : M | ‖(Φ₀ (f x)).2.2.1‖ < ε} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.comp (continuous_snd.comp
        (continuous_snd.comp hΦ₀fc)))) continuous_const
    rw [hU₁'def]
    exact (hU₁o.inter h1).inter h2
  have hU₁'W : U₁' ⊆ W := fun x hx => hU₁W hx.1.1
  have hU₁'row : ∀ x : M, x ∈ U₁' →
      Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} := by
    intro x hx
    obtain ⟨⟨hxU, hxA⟩, hxB⟩ := hx
    have hP : Φ₀ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} :=
      hU₁row x hxU
    have hξeq : Φ₀ (f x) = ((Φ₀ (f x)).1, (0 : ℝ), (Φ₀ (f x)).2.2.1,
        (0 : EuclideanSpace ℝ (Fin k))) := by
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
      · exact hP.1
      · exact hP.2
    have hgfix : Θg (Φ₀ (f x)) = Φ₀ (f x) := by
      conv_lhs => rw [hξeq]
      rw [hplane0 _ _ (le_of_lt hxA) (le_of_lt hxB), hξeq]
    have hfix : Θgi (Φ₀ (f x)) = Φ₀ (f x) := by
      calc Θgi (Φ₀ (f x)) = Θgi (Θg (Φ₀ (f x))) := by rw [hgfix]
        _ = Φ₀ (f x) := hlΘ _
    change Θgi (Φ₀ (f x)) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
    rw [hfix]
    exact hP
  have hseg' : ∀ x : ℝ, |x| ≤ 1 → ∃ z : M, z ∈ U₁' ∧ Φ₀ (f z) = (x, 0, 0, 0) := by
    intro x hx
    obtain ⟨z, hzU, hzv⟩ := hseg x (by linarith [hx, hδ₀])
    refine ⟨z, ⟨⟨hzU, ?_⟩, ?_⟩, hzv⟩
    · show |(Φ₀ (f z)).1| < X'
      rw [hzv]
      have hlt : |x| < X' := by linarith
      simpa using hlt
    · show ‖(Φ₀ (f z)).2.2.1‖ < ε
      rw [hzv]
      simpa using hε
  have hp₂U : fingerParam c₂ r ((-1 : ℝ), 0) ∉ U₁' := fun h => hp₂U₀ h.1.1
  have hq₂U : fingerParam c₂ r ((1 : ℝ), 0) ∉ U₁' := fun h => hq₂U₀ h.1.1
  -- ### the cover row of the isolation
  have hcover : ∀ z : M, Φ₀ (f z) ∈ Δ '' (Work.Drive.PushDisc.lensK \ Work.Drive.PushDisc.lensKo)
      → z ∈ U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X' := by
    intro z hz
    obtain ⟨p, hpK, hzp⟩ := hz
    obtain ⟨hp1, hp2, hp3⟩ := hpK.1
    by_cases hy : p.2 = 0
    · -- bottom edge: covered by the tube, through `hseg'` and `hclean`
      obtain ⟨w, hwU, hwv⟩ := hseg' p.1 hp1
      have hzval : Φ₀ (f z) = ((p.1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) := by
        have hp_eq : p = (p.1, 0) := by rw [← hy]
        rw [← hzp, hp_eq, hΔ0]
      have hfw : f w = f z := hΦ₀inj (by rw [hwv, hzval])
      have hzW : z ∈ W := by
        by_contra hznW
        exact hsep w z (hU₁'W hwU) hznW hfw
      rcases hclean w z (hU₁'W hwU) hzW hfw with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h ▸ hwU)
      · exact Or.inr ⟨((-1 : ℝ), 0), hmem_neg, by rw [h2]; exact hp₂f⟩
      · exact absurd (h1 ▸ hwU) (hp₂f ▸ hp₂U)
      · exact Or.inr ⟨((1 : ℝ), 0), hmem_pos, by rw [h2]; exact hq₂f⟩
      · exact absurd (h1 ▸ hwU) (hq₂f ▸ hq₂U)
    · -- top edge: the disc's top edge is the finger (`hΔ1`), and `hclean` does the rest
      have hp2pos : 0 < p.2 := lt_of_le_of_ne hp2 (Ne.symm hy)
      have habs1 : |p.1| < 1 := by
        by_contra hcon
        have h1 : |p.1| = 1 := le_antisymm hp1 (not_lt.mp hcon)
        have harch : Work.Drive.PushDisc.arch p.1 = 0 := by
          have h2 : p.1 = 1 ∨ p.1 = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1
          rcases h2 with h2 | h2 <;> simp [Work.Drive.PushDisc.arch, h2]
        linarith [hp3]
      have harch : p.2 = Work.Drive.PushDisc.arch p.1 := by
        by_contra hne
        exact hpK.2 ⟨habs1, hp2pos, lt_of_le_of_ne hp3 hne⟩
      have hzval : Φ₀ (f z) = Φ₀ (f (fingerParam c₂ r (p.1, 0))) := by
        have h1 : Φ₀ (f z) = Δ (p.1, Work.Drive.PushDisc.arch p.1) := by
          rw [← hzp]
          show Δ (p.1, p.2) = Δ (p.1, Work.Drive.PushDisc.arch p.1)
          rw [harch]
        have h2 : Δ (p.1, Work.Drive.PushDisc.arch p.1)
            = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (p.1,
                (0 : EuclideanSpace ℝ (Fin k)))))) :=
          hΔ1 p.1 (le_of_lt (habs1.trans hX'))
        rw [h1, h2]
        congr 1
        rw [show fingerParam c₂ r (p.1, 0)
          = c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • (0 : EuclideanSpace ℝ (Fin k))))
          from rfl, smul_zero]
      have huin : fingerParam c₂ r (p.1, 0) ∈ W :=
        hW₀W ⟨(p.1, 0), ⟨habs1.trans hX', by simp⟩, rfl⟩
      have hfz : f (fingerParam c₂ r (p.1, 0)) = f z := (hΦ₀inj hzval).symm
      have hzW : z ∈ W := by
        by_contra hznW
        exact hsep _ z huin hznW hfz
      rcases hclean _ z huin hzW hfz with
        h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨(p.1, 0), ⟨habs1.trans hX', by simp⟩, h⟩
      · exact Or.inr ⟨((-1 : ℝ), 0), hmem_neg, by rw [h2]; exact hp₂f⟩
      · exfalso
        have hpp : fingerParam c₂ r (p.1, 0) = fingerParam c₂ r ((-1 : ℝ), 0) := by
          rw [h1, hp₂f]
        have hpair := hσ₂inj ⟨habs1.trans hX', by simp⟩ hmem_neg hpp
        have hfst : p.1 = -1 := congrArg Prod.fst hpair
        have hzero : Work.Drive.PushDisc.arch p.1 = 0 := by
          rw [hfst]; norm_num [Work.Drive.PushDisc.arch]
        linarith [hp2pos]
      · exact Or.inr ⟨((1 : ℝ), 0), hmem_pos, by rw [h2]; exact hq₂f⟩
      · exfalso
        have hpp : fingerParam c₂ r (p.1, 0) = fingerParam c₂ r ((1 : ℝ), 0) := by
          rw [h1, hq₂f]
        have hpair := hσ₂inj ⟨habs1.trans hX', by simp⟩ hmem_pos hpp
        have hfst : p.1 = 1 := congrArg Prod.fst hpair
        have hzero : Work.Drive.PushDisc.arch p.1 = 0 := by
          rw [hfst]; norm_num [Work.Drive.PushDisc.arch]
        linarith [hp2pos]
  -- ### the isolation
  have hgcont : Continuous (fun z : M => Φ₀ (f z)) := hΦ₀fc
  have hΔcont : ContinuousOn Δ Work.Drive.PushDisc.lensK := hΔsm.continuous.continuousOn
  have hDint : Δ '' Work.Drive.PushDisc.lensKo ∩ (fun z : M => Φ₀ (f z)) '' (Set.univ : Set M)
      = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨⟨q, hq, hqa⟩, z, -, hza⟩
    exact hΔclean z ⟨q, hq, hqa.trans hza.symm⟩
  have hVopen : IsOpen (U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X') :=
    hU₁'o.union (hW₀o X' hX' le_rfl)
  obtain ⟨δ, hδpos, hδ⟩ := exists_isolation_of_cleanRegion (fun z : M => Φ₀ (f z)) hgcont Δ
    Work.Drive.PushDisc.lensK isCompact_lensK hΔcont Work.Drive.PushDisc.lensKo
    Work.Drive.PushDisc.lensKo_subset_lensK hDint
    (U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X') hVopen hcover
  -- ### the thin neighbourhood `V`
  set V : Set (Work.Drive.Whitney.Mdl k) :=
    {ξ | ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ} with hVdef
  have hVo : IsOpen V := by
    rw [hVdef]
    rw [show {ξ : Work.Drive.Whitney.Mdl k |
          ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ}
        = ⋃ a ∈ Δ '' Work.Drive.PushDisc.lensK, Θg ⁻¹' Metric.ball a δ from by
      ext ξ
      simp [Set.mem_iUnion, Set.mem_preimage, Metric.mem_ball]]
    exact isOpen_biUnion (fun a _ => Metric.isOpen_ball.preimage hΘgsm.continuous)
  have hVD : Work.Drive.PushDisc.asymDisc k Work.Drive.PushDisc.arch ⊆ V := by
    intro ξ hξ
    obtain ⟨hx1, hy0, hxy, hu0, hv0⟩ := hξ
    show ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ
    refine ⟨Δ (ξ.1, ξ.2.1), ⟨(ξ.1, ξ.2.1), ⟨hx1, hy0, hxy⟩, rfl⟩, ?_⟩
    have hξeq : ξ = (ξ.1, ξ.2.1, (0 : EuclideanSpace ℝ (Fin k)),
        (0 : EuclideanSpace ℝ (Fin k))) :=
      Prod.ext rfl (Prod.ext rfl (Prod.ext hu0 hv0))
    rw [hξeq, hdisc ξ.1 ξ.2.1 (by linarith [hx1, hX']) hy0 hxy, dist_self]
    exact hδpos
  have hVthin : ∀ z : M, Φ (f z) ∈ V →
      z ∈ U₁' ∨ z ∈ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X' := by
    intro z hz
    rw [hVdef] at hz
    obtain ⟨a, ha, hdist⟩ := hz
    have hΘΦz : Θg (Φ (f z)) = Φ₀ (f z) := by
      change Θg (Θgi (Φ₀ (f z))) = Φ₀ (f z)
      exact hrΘ (Φ₀ (f z))
    rw [hΘΦz] at hdist
    rcases hδ z ⟨a, ha, hdist⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W := by
    intro z hz
    rcases hVthin z hz with h | h
    · exact hU₁'W h
    · exact hW₀W h
  -- ### the chart obligation
  refine ⟨hfp, hfq, hclean, k, rfl, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, fingerHeight k, hh,
    fingerParam c₂ r, hσ₂row, hp₂f, hq₂f, hW₀o, hW₀W, Work.Drive.PushDisc.arch, contDiff_arch,
    hcore, hlip, ?_, ?_, ?_, ?_, hfrontier, ?_, ?_, D, (fun p => Φ (D p)), (fun p => rfl),
    hDclean, U₁', hU₁'o, hU₁'row, V, hVo, hVD, hVW, hVthin⟩
  · norm_num [Work.Drive.PushDisc.arch]
  · norm_num [Work.Drive.PushDisc.arch]
  · intro x hx
    exact arch_pos hx
  · intro x h1 _
    exact arch_neg h1
  · rw [hp₁c]
    change Θ₀ ((-1 : ℝ), 0, 0, 0) = Θ₀ (Θg ((-1 : ℝ), 0, 0, 0))
    rw [hΘg_neg]
  · rw [hq₁c]
    change Θ₀ ((1 : ℝ), 0, 0, 0) = Θ₀ (Θg ((1 : ℝ), 0, 0, 0))
    rw [hΘg_pos]



end

end Work.Drive.PushDisc
