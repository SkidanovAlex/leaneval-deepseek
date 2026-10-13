import Mathlib
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC5.S4ExpG.EmbedComm
import Submission.Work.WilC5.S4ExpG.OrderEmbed

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilC5.S4ExpG

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **Log-preservation of the extension `A ↦ Dcl(A ∪ {exp a})`** (vdDMM Lemma 4.3, last step).

`K, L ⊨ T_E` with the canonical `L_Rc`-data (`hrexpK`, `haddK`, …, `hlenegL`; note the `rexp`
symbol of both models *is* `rexpFromExp` by `hrexpK`/`hrexpL`).  `A ⊆ K` is `Dcl`-closed and
log-closed, `B ≤ K` is a substructure with carrier `A`, `a : B`, and `expE a ∉ A`.

`hVA` is the value-theoretic input of Lemma 4.3 (`Work.WilC5.S4Exp.va_exp`): every nonzero element
of `Dcl (A ∪ {expE a})` decomposes as `w^Q = z · (expE a)^N · (1 + ε)`, `Q > 0`, `z ∈ A \ {0}`,
`ε` infinitesimal.

`τ : B ↪ L` is log-preserving on `B` (`hτlog`), `S ≤ K` is the substructure with carrier
`Dcl (A ∪ {expE a})` — hence `Dcl`-closed (`hSdcl`) and log-closed (`hlogcl`) — and
`σ' : S ↪ L` extends `τ` on `B = A` (`hσ'B`) and sends `expE a` to `expE (τ a)` (`hσ'x`).

Then `σ'` commutes with the definable logarithm on `S`.

Proof sketch.  For `w ∈ S` with `¬ (0 < w)` both sides are `0` (`logFun` vanishes off the positive
elements; `σ'` preserves the order, being an embedding of models of `TR`).  For `0 < w`, take the
decomposition and apply `logFun` on `K`:

  `Q · logFun w = logFun z + N · a + logFun (1 + ε)`,   (∗)

using `logFun (u ^ Q) = Q · logFun u` for `u > 0` (`Work.WilC5.S4ExpF.logFun_zpow`), the
additivity of `logFun` on positive factors (`logFun_mul`), `logFun (expE a) = a`, and
`logFun_one_add_rexp` for the last term; `1 + ε ∈ S` (whence `logFun (1+ε) ∈ S`) follows from
`hS`/`hSdcl` and the decomposition.  Applying the embedding `σ'` to (∗) and using the same
identities on the image decomposition `(σ' w)^Q = (σ' z) · (expE (τ a))^N · σ'(1+ε)` gives

  `Q · logFun (σ' w) = σ' (logFun z + N·a + logFun (1+ε)) = Q · σ' (logFun w)`,

where the middle step needs `logFun (σ' (1+ε)) = σ' (logFun (1+ε))`: both are the unique `v` with
`rexpFromExp v = σ'(1+ε)` (`rexpFromExp (σ'(logFun (1+ε))) = σ'(rexpFromExp (logFun (1+ε)))
= σ'(1+ε)` uses `hrexpK`, `hrexpL` and the fact that `σ'` preserves the `rexp` symbol), and
uniqueness is `logFun_eq_of_rexp_eq`.  Finally divide by `Q ≠ 0`. -/
theorem logPreserving_exp_aux {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (hTEK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hTEL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hlenegK : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    (hlenegL : ∀ x y : L, Work.WilC5.leE x y ↔ x ≤ y)
    (A : Set K) (hAdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) A ⊆ A)
    (hAlog : ∀ x ∈ A, Work.WilC5.logFun x ∈ A)
    (B : WilkiesDesign.CG.LRc.Substructure K) (hB : (B : Set K) = A)
    (hBlog : ∀ x ∈ (B : Set K), Work.WilC5.logFun x ∈ (B : Set K))
    (a : ↥B) (hxa : Work.WilC5.expE (a : K) ∉ A)
    (hVA : ∀ w ∈ @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ)
        (A ∪ {Work.WilC5.expE (a : K)}), w ≠ 0 →
        ∃ Q : ℤ, 0 < Q ∧ ∃ N : ℤ, ∃ z ∈ A, z ≠ 0 ∧ ∃ ε : K, Work.WilC5.IsInfinitesimal ε ∧
          w ^ Q = z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε))
    (τ : WilkiesDesign.CG.LRc.Embedding B L)
    (hτlog : ∀ x : B, τ ⟨Work.WilC5.logFun (x : K), hBlog (x : K) x.2⟩ = Work.WilC5.logFun (τ x))
    (S : WilkiesDesign.CG.LRc.Substructure K) (hS : (S : Set K) =
      @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (A ∪ {Work.WilC5.expE (a : K)}))
    (hSdcl : @Work.WilC2.Dcl K (WilkiesDesign.CG.LR.withConstantsStructure ℝ) (S : Set K) ⊆ (S : Set K))
    (hlogcl : ∀ w ∈ (S : Set K), Work.WilC5.logFun w ∈ (S : Set K))
    (hBleS : B ≤ S)
    (hxS : Work.WilC5.expE (a : K) ∈ (S : Set K))
    (σ' : WilkiesDesign.CG.LRc.Embedding S L)
    (hσ'B : ∀ b : B, σ' ⟨(b : K), hBleS b.2⟩ = τ b)
    (hσ'x : σ' ⟨Work.WilC5.expE (a : K), hxS⟩ = Work.WilC5.expE (τ a)) :
    ∀ w : S, σ' ⟨Work.WilC5.logFun (w : K), hlogcl (w : K) w.2⟩ = Work.WilC5.logFun (σ' w) := by
  classical
  intro w
  -- ## Order preservation of `σ'` (via o-minimality and model completeness of `TR`)
  obtain ⟨hσ'le, hσ'pos⟩ := lpOrderEmbed hMCr hOM S hSdcl σ'
  -- ## Membership bookkeeping: the carrier of `S` is `Dcl (A ∪ {expE a})`
  have hwD : (w : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
    hS ▸ w.2
  have dclToS : ∀ ⦃x : K⦄, x ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ)
      (A ∪ {expE (a : K)}) → x ∈ (S : Set K) := by
    intro x hx; rw [hS]; exact hx
  have h0D : (0 : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
    Work.WilC5.S4ExpF.dcl_zero_mem _
  have h1D : (1 : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
    Work.WilC5.S4ExpF.dcl_one_mem _
  have h0S : (0 : K) ∈ (S : Set K) := dclToS h0D
  have h1S : (1 : K) ∈ (S : Set K) := dclToS h1D
  have hneg1S : (-1 : K) ∈ (S : Set K) := by
    have h := dclToS (Work.WilC5.S4ExpF.dcl_neg_mem _ h1D)
    simpa using h
  have hnatS : ∀ n : ℕ, (((n : ℕ) : K)) ∈ (S : Set K) := fun n =>
    dclToS (Work.WilC5.S4ExpF.dcl_natCast_mem _ n)
  have hintS : ∀ i : ℤ, ((i : ℤ) : K) ∈ (S : Set K) := fun i =>
    dclToS (Work.WilC5.S4ExpF.dcl_intCast_mem _ i)
  have haD : (a : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
    Work.WilC2.subset_dcl_aux _ (Or.inl (hB ▸ a.2))
  have haS : (a : K) ∈ (S : Set K) := dclToS haD
  have hxaD : Work.WilC5.expE (a : K) ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ)
      (A ∪ {Work.WilC5.expE (a : K)}) := Work.WilC2.subset_dcl_aux _ (Or.inr rfl)
  by_cases hpos : 0 < (w : K)
  · -- ============================ the positive case ============================
    obtain ⟨Q, hQ, N, z, hzA, hz0, ε, hε, hdec⟩ := hVA (w : K) hwD (ne_of_gt hpos)
    -- positivity in `K`
    have hexp_pos : 0 < Work.WilC5.expE (a : K) :=
      (Work.WilC5.S4ExpF.leE_zero_iff hTEK haddK hlenegK (Work.WilC5.expE (a : K))).mp
        (Work.WilC5.expE_pos_of_model hTEK (a : K))
    have hε_half : |ε| ≤ (2 : K)⁻¹ := by
      have h := hε 1
      rw [show (((1 : ℕ) : K) + 1) = 2 by norm_num] at h
      exact h
    have h1ε_pos : 0 < 1 + ε := by
      have hlow : -(2 : K)⁻¹ ≤ ε := (abs_le.mp hε_half).1
      have h2inv : (2 : K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by norm_num : (1 : K) < 2)
      linarith
    have hexNpos : 0 < (Work.WilC5.expE (a : K)) ^ N := zpow_pos hexp_pos N
    have hwQpos : 0 < (w : K) ^ Q := zpow_pos hpos Q
    have hzpos : 0 < z := by
      have hprod : 0 < (z * (Work.WilC5.expE (a : K)) ^ N) * (1 + ε) := by
        rw [← hdec]; exact hwQpos
      have h1 : 0 < z * (Work.WilC5.expE (a : K)) ^ N :=
        (mul_pos_iff_of_pos_right h1ε_pos).mp hprod
      exact (mul_pos_iff_of_pos_right hexNpos).mp h1
    -- membership in `S` of the elements of the decomposition
    have hzD : z ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
      Work.WilC2.subset_dcl_aux _ (Or.inl hzA)
    have hzS : z ∈ (S : Set K) := dclToS hzD
    have hden0 : z * (Work.WilC5.expE (a : K)) ^ N ≠ 0 :=
      mul_ne_zero hz0 (zpow_ne_zero N (ne_of_gt hexp_pos))
    have hzexpD : z * (Work.WilC5.expE (a : K)) ^ N ∈
        @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
      Work.WilC5.S4ExpF.dcl_mul_mem _ hzD
        (Work.WilC5.S4ExpF.dcl_zpow_mem _ hxaD (ne_of_gt hexp_pos) N)
    have hzexpS : z * (Work.WilC5.expE (a : K)) ^ N ∈ (S : Set K) := dclToS hzexpD
    have h1εD : 1 + ε ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ)
        (A ∪ {expE (a : K)}) := by
      have h : (w : K) ^ Q * (z * (Work.WilC5.expE (a : K)) ^ N)⁻¹ ∈
          @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
        Work.WilC5.S4ExpF.dcl_mul_mem _ (Work.WilC5.S4ExpF.dcl_zpow_mem _ hwD (ne_of_gt hpos) Q)
          (Work.WilC5.S4ExpF.dcl_inv_mem _ hzexpD hden0)
      have heq : (w : K) ^ Q * (z * (Work.WilC5.expE (a : K)) ^ N)⁻¹ = 1 + ε := by
        rw [hdec, mul_comm (z * (Work.WilC5.expE (a : K)) ^ N) (1 + ε)]
        exact mul_inv_cancel_right₀ hden0 (1 + ε)
      rwa [heq] at h
    have h1εS : 1 + ε ∈ (S : Set K) := dclToS h1εD
    have hεD : ε ∈ @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) := by
      have h := Work.WilC5.S4ExpF.dcl_add_mem _ h1εD
        (Work.WilC5.S4ExpF.dcl_neg_mem _ h1D)
      rwa [show (1 + ε) + (-(1 : K)) = ε from by ring] at h
    have hεS : ε ∈ (S : Set K) := dclToS hεD
    have h2εS : (2 : K) * ε ∈ (S : Set K) :=
      dclToS (Work.WilC5.S4ExpF.dcl_mul_mem _ (Work.WilC5.S4ExpF.dcl_natCast_mem _ 2) hεD)
    have h2S : (((2 : ℕ) : K)) ∈ (S : Set K) := hnatS 2
    have hprodD : z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε) ∈
        @Work.WilC2.Dcl K (LR.withConstantsStructure ℝ) (A ∪ {expE (a : K)}) :=
      Work.WilC5.S4ExpF.dcl_mul_mem _ hzexpD h1εD
    have hprodS : z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε) ∈ (S : Set K) := dclToS hprodD
    have hwPowS : ∀ n : ℕ, (w : K) ^ n ∈ (S : Set K) := fun n =>
      dclToS (Work.WilC5.S4ExpF.dcl_pow_nat_mem _ hwD n)
    have hwZpowS : ∀ i : ℤ, (w : K) ^ i ∈ (S : Set K) := fun i =>
      dclToS (Work.WilC5.S4ExpF.dcl_zpow_mem _ hwD (ne_of_gt hpos) i)
    have hexpPowS : ∀ n : ℕ, (Work.WilC5.expE (a : K)) ^ n ∈ (S : Set K) := fun n =>
      dclToS (Work.WilC5.S4ExpF.dcl_pow_nat_mem _ hxaD n)
    have hexpZpowS : ∀ i : ℤ, (Work.WilC5.expE (a : K)) ^ i ∈ (S : Set K) := fun i =>
      dclToS (Work.WilC5.S4ExpF.dcl_zpow_mem _ hxaD (ne_of_gt hexp_pos) i)
    have hlwS : Work.WilC5.logFun (w : K) ∈ (S : Set K) := hlogcl _ w.2
    have hlzS : Work.WilC5.logFun z ∈ (S : Set K) := hlogcl _ hzS
    have hl1S : Work.WilC5.logFun (1 + ε) ∈ (S : Set K) := hlogcl _ h1εS
    have hQS : (Q : K) ∈ (S : Set K) := hintS Q
    have hNS : (N : K) ∈ (S : Set K) := hintS N
    have hNaS : (N : K) * (a : K) ∈ (S : Set K) :=
      dclToS (Work.WilC5.S4ExpF.dcl_mul_mem _ (Work.WilC5.S4ExpF.dcl_intCast_mem _ N) haD)
    have hzNaS : Work.WilC5.logFun z + (N : K) * (a : K) ∈ (S : Set K) :=
      dclToS (Work.WilC5.S4ExpF.dcl_add_mem _ (hS ▸ hlzS) (hS ▸ hNaS))
    have hbigS : (Q : K) * Work.WilC5.logFun (w : K) ∈ (S : Set K) :=
      dclToS (Work.WilC5.S4ExpF.dcl_mul_mem _ (Work.WilC5.S4ExpF.dcl_intCast_mem _ Q)
        (hS ▸ hlwS))
    have hsumS : Work.WilC5.logFun z + (N : K) * (a : K) + Work.WilC5.logFun (1 + ε) ∈
        (S : Set K) :=
      dclToS (Work.WilC5.S4ExpF.dcl_add_mem _ (hS ▸ hzNaS) (hS ▸ hl1S))
    -- ## the `logFun`-identity on the `K`-side
    have hkeyK : (Q : K) * Work.WilC5.logFun (w : K) =
        Work.WilC5.logFun z + (N : K) * (a : K) + Work.WilC5.logFun (1 + ε) := by
      have h1 : Work.WilC5.logFun ((w : K) ^ Q) = (Q : K) * Work.WilC5.logFun (w : K) :=
        Work.WilC5.S4ExpF.logFun_zpow hTEK haddK hmulK honeK hlenegK (w : K) hpos Q
      have h2 : Work.WilC5.logFun ((Work.WilC5.expE (a : K)) ^ N) =
          (N : K) * Work.WilC5.logFun (Work.WilC5.expE (a : K)) :=
        Work.WilC5.S4ExpF.logFun_zpow hTEK haddK hmulK honeK hlenegK (Work.WilC5.expE (a : K))
          hexp_pos N
      rw [← h1, hdec]
      rw [Work.WilC5.S4ExpF.logFun_mul_pos hTEK haddK hmulK hlenegK (mul_pos hzpos hexNpos)
        h1ε_pos]
      rw [Work.WilC5.S4ExpF.logFun_mul_pos hTEK haddK hmulK hlenegK hzpos hexNpos]
      rw [h2, Work.WilC5.logFun_expE hTEK (a : K)]
    -- ## the image of the decomposition under `σ'`
    have hdecS : (⟨(w : K) ^ Q, hwZpowS Q⟩ : ↥S)
        = ⟨z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε), hprodS⟩ := Subtype.ext hdec
    have hσ'wQ : σ' ⟨(w : K) ^ Q, hwZpowS Q⟩ = (σ' w) ^ Q :=
      lpEmbed_zpow S σ' w (ne_of_gt hpos) hwZpowS hwPowS h1S Q
    have hprod1 : σ' ⟨z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε), hprodS⟩
        = σ' ⟨z * (Work.WilC5.expE (a : K)) ^ N, hzexpS⟩ * σ' ⟨1 + ε, h1εS⟩ :=
      lpEmbed_mul S σ' ⟨z * (Work.WilC5.expE (a : K)) ^ N, hzexpS⟩ ⟨1 + ε, h1εS⟩ hprodS
    have hprod2 : σ' ⟨z * (Work.WilC5.expE (a : K)) ^ N, hzexpS⟩
        = σ' ⟨z, hzS⟩ * σ' ⟨(Work.WilC5.expE (a : K)) ^ N, hexpZpowS N⟩ :=
      lpEmbed_mul S σ' ⟨z, hzS⟩ ⟨(Work.WilC5.expE (a : K)) ^ N, hexpZpowS N⟩ hzexpS
    have hprod3 : σ' ⟨(Work.WilC5.expE (a : K)) ^ N, hexpZpowS N⟩
        = (Work.WilC5.expE (τ a)) ^ N := by
      rw [lpEmbed_zpow S σ' ⟨Work.WilC5.expE (a : K), hxS⟩ (ne_of_gt hexp_pos) hexpZpowS
        hexpPowS h1S N, hσ'x]
    have hLdec : (σ' w) ^ Q = σ' ⟨z, hzS⟩ * (Work.WilC5.expE (τ a)) ^ N * σ' ⟨1 + ε, h1εS⟩ := by
      calc (σ' w) ^ Q = σ' ⟨(w : K) ^ Q, hwZpowS Q⟩ := hσ'wQ.symm
        _ = σ' ⟨z * (Work.WilC5.expE (a : K)) ^ N * (1 + ε), hprodS⟩ := congrArg σ' hdecS
        _ = (σ' ⟨z, hzS⟩ * (Work.WilC5.expE (τ a)) ^ N) * σ' ⟨1 + ε, h1εS⟩ := by
              rw [hprod1, hprod2, hprod3]
        _ = σ' ⟨z, hzS⟩ * (Work.WilC5.expE (τ a)) ^ N * σ' ⟨1 + ε, h1εS⟩ := rfl
    -- ## the `logFun`-identity on the `L`-side
    have hσ'wpos : 0 < (σ' w : L) := (hσ'pos w).mp hpos
    have hσ'zpos : 0 < (σ' ⟨z, hzS⟩ : L) := (hσ'pos ⟨z, hzS⟩).mp hzpos
    have hσ'u1pos : 0 < (σ' ⟨1 + ε, h1εS⟩ : L) :=
      (hσ'pos ⟨1 + ε, h1εS⟩).mp h1ε_pos
    have hexpτpos : 0 < Work.WilC5.expE (τ a) :=
      (Work.WilC5.S4ExpF.leE_zero_iff hTEL haddL hlenegL (Work.WilC5.expE (τ a))).mp
        (Work.WilC5.expE_pos_of_model hTEL (τ a))
    have hkeyL : (Q : L) * Work.WilC5.logFun (σ' w) =
        Work.WilC5.logFun (σ' ⟨z, hzS⟩) + (N : L) * (τ a)
          + Work.WilC5.logFun (σ' ⟨1 + ε, h1εS⟩) := by
      have h1 : Work.WilC5.logFun ((σ' w) ^ Q) = (Q : L) * Work.WilC5.logFun (σ' w) :=
        Work.WilC5.S4ExpF.logFun_zpow hTEL haddL hmulL honeL hlenegL (σ' w) hσ'wpos Q
      have h2 : Work.WilC5.logFun ((Work.WilC5.expE (τ a)) ^ N) =
          (N : L) * Work.WilC5.logFun (Work.WilC5.expE (τ a)) :=
        Work.WilC5.S4ExpF.logFun_zpow hTEL haddL hmulL honeL hlenegL (Work.WilC5.expE (τ a))
          hexpτpos N
      rw [← h1, hLdec]
      rw [Work.WilC5.S4ExpF.logFun_mul_pos hTEL haddL hmulL hlenegL
        (mul_pos hσ'zpos (zpow_pos hexpτpos N)) hσ'u1pos]
      rw [Work.WilC5.S4ExpF.logFun_mul_pos hTEL haddL hmulL hlenegL hσ'zpos
        (zpow_pos hexpτpos N)]
      rw [h2, Work.WilC5.logFun_expE hTEL (τ a)]
    -- ## the pieces of the image of the `K`-side identity
    have hzB : z ∈ (B : Set K) := hB.symm ▸ hzA
    have hτlog_z : σ' ⟨Work.WilC5.logFun z, hlzS⟩ = Work.WilC5.logFun (σ' ⟨z, hzS⟩) := by
      have h1 : σ' ⟨Work.WilC5.logFun z, hBleS (hBlog z hzB)⟩
          = τ ⟨Work.WilC5.logFun z, hBlog z hzB⟩ := hσ'B ⟨Work.WilC5.logFun z, hBlog z hzB⟩
      have h2 : τ ⟨Work.WilC5.logFun z, hBlog z hzB⟩ = Work.WilC5.logFun (τ ⟨z, hzB⟩) :=
        hτlog ⟨z, hzB⟩
      have h3 : τ ⟨z, hzB⟩ = σ' ⟨z, hzS⟩ := by
        have h := hσ'B ⟨z, hzB⟩
        rw [h.symm]
      calc σ' ⟨Work.WilC5.logFun z, hlzS⟩
          = σ' ⟨Work.WilC5.logFun z, hBleS (hBlog z hzB)⟩ :=
            congrArg σ' (Subtype.ext rfl)
        _ = τ ⟨Work.WilC5.logFun z, hBlog z hzB⟩ := h1
        _ = Work.WilC5.logFun (τ ⟨z, hzB⟩) := h2
        _ = Work.WilC5.logFun (σ' ⟨z, hzS⟩) := by rw [h3]
    have hσ'a : σ' ⟨(a : K), haS⟩ = τ a := by
      have h := hσ'B a
      rw [h]
    have hNaσ' : σ' ⟨(N : K) * (a : K), hNaS⟩ = (N : L) * (τ a) := by
      rw [lpEmbed_mul S σ' ⟨(N : K), hNS⟩ ⟨(a : K), haS⟩ hNaS, lpEmbed_intCast S σ' hintS N, hσ'a]
    -- ## the crux: `σ'` commutes with `logFun` at `1 + ε`
    have hcrux : σ' ⟨Work.WilC5.logFun (1 + ε), hl1S⟩ = Work.WilC5.logFun (σ' ⟨1 + ε, h1εS⟩) := by
      have hδ1 : Work.WilC5.absLeOne (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE
          Work.WilC5.oneE) ε) := by
        have hmulE : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε
            = (2 : K) * ε := by
          rw [haddK, honeK, hmulK]; norm_num
        rw [hmulE, Work.WilC5.S4ExpF.absLeOne_iff_abs hTEK haddK honeK hlenegK, abs_mul,
          abs_of_pos (by norm_num : (0 : K) < 2)]
        calc (2 : K) * |ε| ≤ (2 : K) * (2 : K)⁻¹ :=
              mul_le_mul_of_nonneg_left hε_half (by norm_num)
          _ = 1 := by field_simp
      have hrexp1 : Work.WilC5.rexpFromExp (Work.WilC5.logFun (1 + ε)) = 1 + ε := by
        have h := Work.WilC5.logFun_one_add_rexp hTEK hδ1
        rwa [haddK, honeK] at h
      have hmemR : Work.WilC5.rexpFromExp (Work.WilC5.logFun (1 + ε)) ∈ (S : Set K) :=
        lpMem_rexp hrexpK hl1S
      have himg : Work.WilC5.rexpFromExp (σ' ⟨Work.WilC5.logFun (1 + ε), hl1S⟩)
          = σ' ⟨1 + ε, h1εS⟩ := by
        rw [← lpEmbed_rexpFromExp hrexpK hrexpL S σ' ⟨Work.WilC5.logFun (1 + ε), hl1S⟩ hmemR,
          show (⟨Work.WilC5.rexpFromExp (Work.WilC5.logFun (1 + ε)), hmemR⟩ : ↥S)
              = ⟨1 + ε, h1εS⟩ from Subtype.ext hrexp1]
      have hu_eq : σ' ⟨1 + ε, h1εS⟩ = 1 + σ' ⟨ε, hεS⟩ := by
        have h := lpEmbed_add S σ' ⟨(1 : K), h1S⟩ ⟨ε, hεS⟩ h1εS
        rw [lpEmbed_one S σ' h1S] at h
        exact h
      have hδ1L : Work.WilC5.absLeOne (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE
          Work.WilC5.oneE) (σ' ⟨ε, hεS⟩)) := by
        have hmulL' : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE)
            (σ' ⟨ε, hεS⟩) = (2 : L) * (σ' ⟨ε, hεS⟩) := by
          rw [haddL, honeL, hmulL]; norm_num
        rw [hmulL', Work.WilC5.S4ExpF.absLeOne_iff_abs hTEL haddL honeL hlenegL]
        have habs : |(2 : K) * ε| ≤ 1 := by
          have ht : Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε
              = (2 : K) * ε := by rw [haddK, honeK, hmulK]; norm_num
          have h := (Work.WilC5.S4ExpF.absLeOne_iff_abs hTEK haddK honeK hlenegK
            (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ε)).mp hδ1
          rwa [ht] at h
        obtain ⟨hlo, hhi⟩ := abs_le.mp habs
        have h2σ : σ' ⟨(2 : K), h2S⟩ = (((2 : ℕ) : L)) := by
          have hv : (2 : K) = (((2 : ℕ) : K)) := by push_cast; ring
          rw [show (⟨(2 : K), h2S⟩ : ↥S) = ⟨(((2 : ℕ) : K)), hnatS 2⟩ from
            Subtype.ext hv, lpEmbed_natCast S σ' hnatS 2]
        have h2εσ : σ' ⟨(2 : K) * ε, h2εS⟩ = (2 : L) * σ' ⟨ε, hεS⟩ := by
          rw [lpEmbed_mul S σ' ⟨(2 : K), h2S⟩ ⟨ε, hεS⟩ h2εS, h2σ]
          norm_num
        rw [← h2εσ, abs_le]
        refine ⟨?_, ?_⟩
        · have h := (hσ'le ⟨(-1 : K), hneg1S⟩ ⟨(2 : K) * ε, h2εS⟩).mp hlo
          have hneg : σ' ⟨(-1 : K), hneg1S⟩ = (-1 : L) := by
            have h' := lpEmbed_neg S σ' ⟨(1 : K), h1S⟩ hneg1S
            rw [lpEmbed_one S σ' h1S] at h'
            simpa using h'
          rwa [hneg] at h
        · have h := (hσ'le ⟨(2 : K) * ε, h2εS⟩ ⟨(1 : K), h1S⟩).mp hhi
          rwa [lpEmbed_one S σ' h1S] at h
      have huniq := Work.WilC5.logFun_eq_of_rexp_eq hTEL (δ := σ' ⟨ε, hεS⟩)
        (u := σ' ⟨Work.WilC5.logFun (1 + ε), hl1S⟩) hδ1L (by rw [himg, hu_eq, haddL, honeL])
      rw [huniq]
      exact congrArg Work.WilC5.logFun (by rw [haddL, honeL, ← hu_eq])
    -- ## applying `σ'` to the `K`-side identity
    have hsumσ' : σ' ⟨Work.WilC5.logFun z + (N : K) * (a : K) + Work.WilC5.logFun (1 + ε),
        hsumS⟩ = Work.WilC5.logFun (σ' ⟨z, hzS⟩) + (N : L) * (τ a)
          + Work.WilC5.logFun (σ' ⟨1 + ε, h1εS⟩) := by
      rw [lpEmbed_add S σ' ⟨Work.WilC5.logFun z + (N : K) * (a : K), hzNaS⟩
          ⟨Work.WilC5.logFun (1 + ε), hl1S⟩ hsumS,
        lpEmbed_add S σ' ⟨Work.WilC5.logFun z, hlzS⟩ ⟨(N : K) * (a : K), hNaS⟩ hzNaS,
        hτlog_z, hNaσ', hcrux]
    -- ## conclusion
    have hfinal : (Q : L) * σ' ⟨Work.WilC5.logFun (w : K), hlwS⟩
        = (Q : L) * Work.WilC5.logFun (σ' w) := by
      calc (Q : L) * σ' ⟨Work.WilC5.logFun (w : K), hlwS⟩
          = σ' ⟨(Q : K) * Work.WilC5.logFun (w : K), hbigS⟩ := by
            rw [lpEmbed_mul S σ' ⟨(Q : K), hQS⟩ ⟨Work.WilC5.logFun (w : K), hlwS⟩ hbigS,
              lpEmbed_intCast S σ' hintS Q]
        _ = σ' ⟨Work.WilC5.logFun z + (N : K) * (a : K) + Work.WilC5.logFun (1 + ε), hsumS⟩ :=
            congrArg σ' (Subtype.ext hkeyK)
        _ = Work.WilC5.logFun (σ' ⟨z, hzS⟩) + (N : L) * (τ a)
              + Work.WilC5.logFun (σ' ⟨1 + ε, h1εS⟩) := hsumσ'
        _ = (Q : L) * Work.WilC5.logFun (σ' w) := hkeyL.symm
    have hQ0 : (Q : L) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hQ)
    rw [show (⟨Work.WilC5.logFun (w : K), hlogcl (w : K) w.2⟩ : ↥S)
        = ⟨Work.WilC5.logFun (w : K), hlwS⟩ from Subtype.ext rfl]
    exact mul_left_cancel₀ hQ0 hfinal
  · -- ============================ the nonpositive case ============================
    have hlogw : Work.WilC5.logFun (w : K) = 0 :=
      Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos hTEK haddK honeK hlenegK (w : K) hpos
    have hσ'w : ¬ 0 < (σ' w : L) := fun h => hpos ((hσ'pos w).mpr h)
    rw [show (⟨Work.WilC5.logFun (w : K), hlogcl (w : K) w.2⟩ : ↥S) = ⟨(0 : K), h0S⟩ from
      Subtype.ext hlogw, lpEmbed_zero S σ' h0S]
    exact (Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos hTEL haddL honeL hlenegL (σ' w) hσ'w).symm

end Work.WilC5.S4ExpG
