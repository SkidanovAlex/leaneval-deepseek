import Mathlib
import Submission.Work.Drive.PushDisc.chartObligation
import Submission.Work.Drive.PushDisc.straightFlatTubeArc
import Submission.Work.Drive.PushDisc.arcInjOnOfHclean
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.fingerChartSolid
import Submission.Work.Drive.PushDisc.fingerDataSafe
import Submission.Work.Drive.PushDisc.lensFramesSolid
import Submission.Work.Drive.PushDisc.lensThetaThinSolid
import Submission.Work.Drive.PushDisc.lensCleanOfChartSolid
import Submission.Work.Drive.PushDisc.flatArcChartSolid
import Submission.Work.Drive.PushDisc.lensAssemblyThinWired
import Submission.Work.Whitney.PushSigned

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold

theorem lensWiringSolid {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hfibp : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂)
    (hfibq : ∀ z : M, f z = f q₁ → z = q₁ ∨ z = q₂)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂) :
    Nonempty (Work.Drive.PushDisc.WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) := by
  classical
  -- ## 0. the configuration bundle
  let C : LWConfig n M :=
    { hn := hn, f := f, hf := hf, himm := himm, W := W, hWopen := hWopen, hWcpt := hWcpt,
      p₁ := p₁, p₂ := p₂, q₁ := q₁, q₂ := q₂, hW₁ := hW₁, hW₂ := hW₂, hW₃ := hW₃, hW₄ := hW₄,
      hp₁p₂ := hp₁p₂, hq₁q₂ := hq₁q₂, hp₁q₁ := hp₁q₁, hp₁q₂ := hp₁q₂, hp₂q₁ := hp₂q₁,
      hp₂q₂ := hp₂q₂, hfp := hfp, hfq := hfq, hclean := hclean, hsep := hsep, hfibp := hfibp,
      hfibq := hfibq, htransP := htransP, htransQ := htransQ, γ₁ := γ₁, γ₂ := γ₂, hγ₁ := hγ₁,
      hγ₂ := hγ₂, hγ₁0 := hγ₁0, hγ₁1 := hγ₁1, hγ₂0 := hγ₂0, hγ₂1 := hγ₂1, hγW₁ := hγW₁,
      hγW₂ := hγW₂, hγ₁inj := hγ₁inj, hγ₂inj := hγ₂inj, hγ₁smooth := hγ₁smooth,
      hγ₂smooth := hγ₂smooth, hγ₁imm := hγ₁imm, hγ₂imm := hγ₂imm, hγdisj := hγdisj,
      hγend := hγend, hsign := hsign }
  -- ## 1. the model dimension
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  -- ## 2. the arc-avoidance rows
  have hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, hs, hsp⟩
    have h2 : (s = 0 ∧ (0 : ℝ) = 0) ∨ (s = 1 ∧ (0 : ℝ) = 1) :=
      hγdisj s hs 0 ⟨le_refl 0, zero_le_one⟩ (by rw [hsp]; exact hγ₂0.symm)
    rcases h2 with h2 | h2
    · have h0 : p₁ = γ₁ s := hγ₁0.symm.trans (by rw [h2.1])
      exact hp₁p₂ (h0.trans hsp)
    · norm_num at h2
  have hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨s, hs, hsp⟩
    have h2 : (s = 0 ∧ (1 : ℝ) = 0) ∨ (s = 1 ∧ (1 : ℝ) = 1) :=
      hγdisj s hs 1 ⟨zero_le_one, le_refl 1⟩ (by rw [hsp]; exact hγ₂1.symm)
    rcases h2 with h2 | h2
    · norm_num at h2
    · have h0 : q₁ = γ₁ s := hγ₁1.symm.trans (by rw [h2.1])
      exact hq₁q₂ (h0.trans hsp)
  have hp₁arc : p₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have h2 : ((0 : ℝ) = 0 ∧ t = 0) ∨ ((0 : ℝ) = 1 ∧ t = 1) :=
      hγdisj 0 ⟨le_refl 0, zero_le_one⟩ t ht (by rw [htp]; exact hγ₁0)
    rcases h2 with h2 | h2
    · have h0 : p₂ = γ₂ t := hγ₂0.symm.trans (by rw [h2.2])
      exact hp₁p₂ (h0.trans htp).symm
    · norm_num at h2
  have hq₁arc : q₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have h2 : ((1 : ℝ) = 0 ∧ t = 0) ∨ ((1 : ℝ) = 1 ∧ t = 1) :=
      hγdisj 1 ⟨zero_le_one, le_refl 1⟩ t ht (by rw [htp]; exact hγ₁1)
    rcases h2 with h2 | h2
    · norm_num at h2
    · have h0 : q₂ = γ₂ t := hγ₂1.symm.trans (by rw [h2.2])
      exact hq₁q₂ (h0.trans htp).symm
  -- ## 3. the flat tube of the first arc (S5)
  obtain ⟨k₁, hk₁, Φ₀, Θ₀, U₁, δ₀, hΦ₀sm, hΘ₀sm, hΘ₀Φ₀, hΦ₀Θ₀, hU₁o, hU₁W, hU₁arc,
    hp₂U₁, hq₂U₁, hU₁row, hδ₀, hseg, hpin₁, hpin₃, harcΦ, -⟩ :=
    straightFlatTubeArc (n := k + 1) (by omega) f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₃
      hp₁p₂ hfp hfq hclean hsep htransP htransQ γ₁ hγ₁ hγ₁0 hγ₁1 hγW₁ hγ₁inj hγ₁smooth hγ₁imm
      hp₂arc hq₂arc
  have hkk : k = k₁ := by omega
  subst hkk
  have hp₁Θ : f p₁ = Θ₀ ((-1 : ℝ), 0, 0, 0) := by rw [← hΘ₀Φ₀ (f p₁), hpin₁]
  have hq₁Θ : f q₁ = Θ₀ ((1 : ℝ), 0, 0, 0) := by rw [← hΘ₀Φ₀ (f q₁), hpin₃]
  have hpin₂ : Φ₀ (f p₂) = ((-1 : ℝ), 0, 0, 0) := by rw [← hfp, hpin₁]
  have hpin₄ : Φ₀ (f q₂) = ((1 : ℝ), 0, 0, 0) := by rw [← hfq, hpin₃]
  let T : LWFlatTube k M C :=
    { Φ₀ := Φ₀, Θ₀ := Θ₀, hΦ₀sm := hΦ₀sm, hΘ₀sm := hΘ₀sm, hΘ₀Φ₀ := hΘ₀Φ₀, hΦ₀Θ₀ := hΦ₀Θ₀,
      U₁ := U₁, hU₁o := hU₁o, hU₁W := hU₁W, hU₁arc := hU₁arc, hp₂U₁ := hp₂U₁, hq₂U₁ := hq₂U₁,
      hU₁row := hU₁row, δ₀ := δ₀, hδ₀ := hδ₀, hseg := hseg, hpin₁ := hpin₁, hpin₂ := hpin₂,
      hpin₃ := hpin₃, hpin₄ := hpin₄, harc₁ := harcΦ }
  -- ## 4. the finger chart, the finger data, the clean lens, the first-arc chart,
  --        the frames and the framing diffeomorphism
  obtain ⟨F⟩ := fingerChartSolid C
  obtain ⟨G⟩ := fingerDataSolidSafe C T F
  obtain ⟨D⟩ := lensCleanOfChartSolid C T F G
  obtain ⟨c₁⟩ := flatArcChartSolid C T
  obtain ⟨Fr⟩ := lensFramesSolid C T F G D c₁
  obtain ⟨Th⟩ := lensThetaThinSolid C T F G D Fr
  -- ## 5. the Whitney disc
  obtain ⟨hγ₁injf, hγ₂injf⟩ :=
    arcInjOnOfHclean f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj
      hγdisj hp₁p₂ hq₁q₂ hclean
  obtain ⟨Dd, hDdsm, hDdclean'⟩ :=
    exists_disc_of_bigonData (n := k + 1) (by omega) f hf himm γ₁ γ₂ hγ₁smooth hγ₂smooth
      (by rw [hγ₁0, hγ₂0, hfp]) (by rw [hγ₁1, hγ₂1, hfq]) hγ₁injf hγ₂injf hγend
  have hDdclean : ∀ z : M, f z ∉ Dd '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have h1 : f z ∈ Dd '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩ f '' (Set.univ : Set M) :=
      ⟨hz, ⟨z, trivial, rfl⟩⟩
    rw [hDdclean'] at h1
    exact h1
  -- ## 6. the thin assembly
  have hcA : Nonempty (ChartObligation (k + 1) f W p₁ p₂ q₁ q₂) := by
    refine lensAssemblyThinWired (n := k + 1) f hf W p₁ p₂ q₁ q₂ hfp hfq hclean hsep
      k rfl Th.X'' Th.hX'' Th.r Th.hr Th.ε Th.hε γ₂ hγ₂ hγ₂0 hγ₂1 hγW₂ Φ₀ Θ₀ hΦ₀sm hΘ₀sm
      hΘ₀Φ₀ hΦ₀Θ₀ U₁ hU₁o hU₁W ?_ δ₀ hδ₀ hseg hp₁Θ hq₁Θ hpin₂ hpin₄
      F.c F.hcsrc ?_ ?_ F.harc₂ ?_ D.Δ D.hΔsm D.hΔ0 ?_ (fun z hz => by
        obtain ⟨q, hq, hqd⟩ := hz
        exact D.hΔclean q hq z hqd)
      Th.Θg Th.Θgi Th.hΘgsm Th.hΘgism Th.hlΘ Th.hrΘ Th.hplane0 Th.hdisc ?_ Dd hDdclean
    · -- the flat-tube row
      intro x hx
      simpa [Work.Drive.Whitney.sheetA] using hU₁row x hx
    · -- `p₂ ∈ c₂.source`
      exact F.hcarc ⟨0, ⟨le_refl 0, zero_le_one⟩, hγ₂0⟩
    · -- `q₂ ∈ c₂.source`
      exact F.hcarc ⟨1, ⟨zero_le_one, le_refl 1⟩, hγ₂1⟩
    · -- the window row
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      have h1 : |p.1| ≤ F.X' := le_of_lt (lt_of_lt_of_le hp1 Th.hX''X')
      have h2 : ‖(Th.r / F.r) • p.2‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos Th.hr F.hr)]
        have h3 : Th.r / F.r ≤ 1 := (div_le_one F.hr).mpr Th.hrρ
        calc Th.r / F.r * ‖p.2‖ ≤ 1 * ‖p.2‖ :=
              mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = ‖p.2‖ := one_mul _
          _ ≤ 1 := le_of_lt hp2
      have h4 := F.hwin (p.1, (Th.r / F.r) • p.2) h1 h2
      have h5 : F.r • ((Th.r / F.r) • p.2) = Th.r • p.2 := by
        rw [smul_smul]
        have hFF : F.r * (Th.r / F.r) = Th.r := by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt F.hr)]
        rw [hFF]
      rwa [h5] at h4
    · -- the disc row
      intro x hx
      rw [D.hΔ1 x (le_trans hx Th.hX''X')]
      exact G.hS₂ag (x, 0) (le_trans hx Th.hX''X') (by simpa using F.hr.le)
    · -- the finger row
      intro x w hx hw
      rw [Th.hfinger x w hx hw]
      refine G.hS₂ag (x, Th.r • w) (le_of_lt (lt_of_lt_of_le hx Th.hX''X')) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos Th.hr]
      calc Th.r * ‖w‖ ≤ Th.r * 1 := mul_le_mul_of_nonneg_left hw.le Th.hr.le
        _ = Th.r := mul_one _
        _ ≤ F.r := Th.hrρ
  -- ## 7. the bridge to the chart data
  obtain ⟨hC⟩ := hcA
  exact nonempty_windowChartData_of_chartObligation hC

end Work.Drive.PushDisc
