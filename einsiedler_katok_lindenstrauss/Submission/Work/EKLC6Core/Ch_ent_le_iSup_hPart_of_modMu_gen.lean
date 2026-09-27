import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLC6Core.BiGenSup.biOrbit_le_iSup_comap_winPart
import Submission.Work.EKLC6Core.BiGenChain.hPart_le_hPart_add_Hcond
import Submission.Work.EKLC6Core.plaquePartitionAux
import Submission.Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero
import Submission.Work.EKLC6Core.ent_eq_iSup_hPart_of_biGen

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The mod-`μ` countable generator theorem.**  Let `T = aDiag t ·` be measure preserving for
the probability `μ` on `X₃`, let `S : ℕ → Set X₃` be a countable Borel family whose *bi-infinite*
`T`-orbit σ-algebra `biOrbit t S` generates the Borel σ-algebra of `X₃` modulo `μ`, and let
`F : ℕ → FinPart X₃` be a refining chain of finite partitions with
`⨆_l partSigma (F l) = generateFrom (range S)`.  Then the chain computes the Kolmogorov–Sinai
entropy of `T`:

`ent μ T ≤ ⨆_l ofReal (hPart μ T (F l))`.

Together with the trivial reverse inequality (the right-hand side is a sub-supremum of the
defining supremum of `ent`) this says `ent μ T = ⨆_l ofReal (hPart μ T (F l))`.

The proof is the classical Kolmogorov–Sinai argument, run against the σ-algebra generated *modulo
`μ`* rather than exactly (the exact form is false at fixed points of the flow, cf.
`plaquePartitionAux`).  For an arbitrary finite partition `Q` and each `l`:

* `hPart μ T Q ≤ hPart μ T (W l) + Hcond μ Q (A l)`, where `W l = ⋁_{1 ≤ b ≤ l} T^{-b} F l` is
  the one-sided window and `A l = ⨆_n comap (T^[n]) (partSigma (W l))` is its past σ-algebra
  (`BiGenChain.hPart_le_hPart_add_Hcond`);
* `hPart μ T (W l) ≤ hPart μ T (F l)` (`BiGenAux.hPart_winPart_le`);
* `A l ↑ ⨆_l A l`, and `⨆_l A l` already contains the whole two-sided orbit of `σ(S)` — for the
  window of length `l` the shifts `T^{-n}(T^{b} σ(F l))` with `1 ≤ b ≤ l` and `n ∈ ℕ` exhaust all
  `T^{m} σ(F l)`, `m ∈ ℤ` — hence `biOrbit t S ≤ ⨆_l A l`;
* therefore every part of `Q` differs from a `(⨆_l A l)`-measurable set by a `μ`-null set
  (`hgen`), so `Hcond μ Q (⨆_l A l) ≤ 0` (`Hcond_le_zero_of_diff_null`), and Lévy's upward
  theorem (`exists_Hcond_le_of_iSup_le_zero`) makes `Hcond μ Q (A l) ≤ ε` for large `l`.

Letting `ε → 0` gives `hPart μ T Q ≤ hPart μ T (F l) + ε`, and taking the supremum over `Q` in
`ℝ≥0∞` yields the claim. -/
theorem Ch_ent_le_iSup_hPart_of_modMu_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (S : ℕ → Set Work.EKLContract.X3) (hS : ∀ n, MeasurableSet (S n))
    (hgen : Work.EKLC6Core.GeneratesModMuSet μ t S)
    (F : ℕ → @Work.EKLContract.FinPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3)
    (hFle : ∀ l, @Work.EKLContract.partSigma Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (F l)
      ≤ MeasurableSpace.generateFrom (Set.range S))
    (hFmono : ∀ l, @Work.EKLContract.partSigma Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (F l)
      ≤ @Work.EKLContract.partSigma Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 (F (l + 1)))
    (hFgen : (⨆ l, @Work.EKLContract.partSigma Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (F l))
      = MeasurableSpace.generateFrom (Set.range S)) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
      ≤ ⨆ l, ENNReal.ofReal (Work.EKLContract.hPart μ
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) (F l)) := by
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  let Tinv : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag (-t) • x
  have hTmeas : Measurable T := hmp.measurable
  have hTinvmeas : Measurable Tinv :=
    (continuous_const_smul (Work.EKLContract.aDiag (-t))).measurable
  have hinv : Function.LeftInverse Tinv T := fun x => Work.EKLContract.aDiag_neg_smul t x
  -- the one-sided windows and their past σ-algebras
  let W : ℕ → @Work.EKLContract.FinPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 :=
    fun l => Work.EKLC6Core.BiGenAux.winPart Tinv hTinvmeas (F l) l
  let A : ℕ → MeasurableSpace Work.EKLContract.X3 :=
    fun l => ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
      (@Work.EKLContract.partSigma Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 (W l))
  have hWmono : ∀ l, @Work.EKLContract.partSigma Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 (W l)
      ≤ @Work.EKLContract.partSigma Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 (W (l + 1)) :=
    fun l => partSigma_winPart_mono Tinv hTinvmeas F hFmono l
  have hAmono : Monotone A := by
    intro l l' hll'
    have hstep : ∀ a b : ℕ, a ≤ b → @Work.EKLContract.partSigma Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 (W a)
        ≤ @Work.EKLContract.partSigma Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 (W b) := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ c _ ih => exact le_trans ih (hWmono c)
    exact iSup_le fun n =>
      (MeasurableSpace.comap_mono (hstep l l' hll')).trans (le_iSup (fun n' : ℕ =>
        MeasurableSpace.comap (T^[n']) (@Work.EKLContract.partSigma Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 (W l'))) n)
  have hAle : ∀ l, A l ≤ Work.EKLContract.instMeasurableSpaceX3 := by
    intro l
    refine iSup_le fun n => ?_
    exact (MeasurableSpace.comap_mono (partSigma_le_mX'
      (mX := Work.EKLContract.instMeasurableSpaceX3) (W l))).trans
      ((hTmeas.iterate n).comap_le)
  -- the σ-algebra bookkeeping: the pasts of the windows already exhaust the bi-infinite orbit
  have hsup : Work.EKLC6Core.biOrbit t S ≤ ⨆ l : ℕ, A l := by
    have h := Work.EKLC6Core.BiGenSup.biOrbit_le_iSup_comap_winPart (X := Work.EKLContract.X3)
      (mX := Work.EKLContract.instMeasurableSpaceX3) T Tinv hinv hTinvmeas
      (MeasurableSpace.generateFrom (Set.range S)) F hFmono hFgen
    simpa only [Work.EKLC6Core.biOrbit] using h
  -- the chain-rule bound for an arbitrary finite partition
  have hmain : ∀ (Q : @Work.EKLContract.FinPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3) (l : ℕ),
      @Work.EKLContract.hPart Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ T Q
        ≤ @Work.EKLContract.hPart Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3
            μ T (F l)
          + @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3
            μ Q (A l) := by
    intro Q l
    have h1 : @Work.EKLContract.hPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ T Q
        ≤ @Work.EKLContract.hPart Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3
            μ T (W l)
          + @Work.EKLContract.Hcond Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ Q (A l) :=
      Work.EKLC6Core.BiGenChain.hPart_le_hPart_add_Hcond
        (X := Work.EKLContract.X3) (mX := Work.EKLContract.instMeasurableSpaceX3)
        (T := T) μ hmp (W l) Q
    have h2 : @Work.EKLContract.hPart Work.EKLContract.X3
        Work.EKLContract.instMeasurableSpaceX3 μ T (W l)
        ≤ @Work.EKLContract.hPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ T (F l) :=
      Work.EKLC6Core.BiGenAux.hPart_winPart_le
        (X := Work.EKLContract.X3) (mX := Work.EKLContract.instMeasurableSpaceX3)
        (T := T) (Tinv := Tinv) μ hinv hmp hTinvmeas (F l) l
    linarith [h1, h2]
  -- every finite partition computes at most the supremum over the chain
  rw [Work.EKLContract.ent]
  refine iSup_le fun Q => ?_
  have hmod : ∀ i : Fin Q.n, ∃ s : Set Work.EKLContract.X3,
      @MeasurableSet Work.EKLContract.X3 (⨆ l : ℕ, A l) s ∧
        μ (Q.parts i \ s) = 0 ∧ μ (s \ Q.parts i) = 0 := by
    intro i
    obtain ⟨E', hE', h1, h2⟩ := hgen (Q.parts i) (Q.measurable i)
    exact ⟨E', hsup E' hE', h1, h2⟩
  have h0 : @Work.EKLContract.Hcond Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ Q (⨆ l : ℕ, A l) ≤ 0 :=
    Work.EKLC6Core.Hcond_le_zero_of_diff_null Q ⟨⨆ l : ℕ, A l⟩ (iSup_le hAle) hmod
  have hconv : ∀ ε : ℝ, 0 < ε → ∃ l : ℕ, @Work.EKLContract.Hcond Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ Q (A l) ≤ ε :=
    fun ε hε => Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero
      (mX := Work.EKLContract.instMeasurableSpaceX3) μ Q A hAmono hAle h0 hε
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨l, hl⟩ := hconv (ε : ℝ) (by exact_mod_cast hε)
  have hGl0 : (0 : ℝ) ≤ @Work.EKLContract.hPart Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ T (F l) :=
    Work.EKLComp.Core.hPart_nonneg μ T (F l)
  have hε0 : (0 : ℝ) ≤ (ε : ℝ) := by positivity
  calc ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
          Work.EKLContract.instMeasurableSpaceX3 μ T Q)
      ≤ ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ T (F l) + (ε : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by linarith [hmain Q l, hl])
    _ = ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ T (F l)) + ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_add hGl0 hε0
    _ = ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ T (F l)) + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ (⨆ l, ENNReal.ofReal (@Work.EKLContract.hPart Work.EKLContract.X3
            Work.EKLContract.instMeasurableSpaceX3 μ T (F l))) + (ε : ℝ≥0∞) :=
        add_le_add (le_iSup (fun l => ENNReal.ofReal (@Work.EKLContract.hPart
          Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 μ T (F l))) l) le_rfl

end Work.EKLC6Core

end
