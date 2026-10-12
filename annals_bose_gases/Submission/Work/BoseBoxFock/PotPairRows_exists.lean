import ChallengeDeps
import Submission.Work.BoseBoxFock.K1exp_sub_K1lim_pairing_le
import Submission.Work.BoseBoxFock.PotChiLin_exists
import Submission.Work.BoseBoxFock.boxSlotSum_linear
import Submission.Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_gen
import Submission.Work.BoseBoxFock.pairRowAssembly
import Submission.Work.BoseFixB1S.bsOneBody_sq_ge_dirichlet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotPairRows_exists` — FS `lem:2ndQuand`, the `Q₂` (pair-row) group, at a
# *chosen* lattice cut-off

### ⚠ SESSION 13 — **THE NODE IS NOW REDUCED TO ONE THEOREM** (read FINDING §13, esp. §13.11)

The body of `PotPairRows_exists` below is `exact PotPairRows_exists_assembly …`
(`pairRowAssembly.lean`, `sorry`-free).  `#print axioms ⊆ [propext, sorryAx, Classical.choice,
Quot.sound]`, the **only** `sorryAx` being

* **`Work.BoseBoxFock.pairRowS3Bound`** (`pairRowS3Bound.lean`) — the *limit-kernel* comparison
  `(rowPairSubC (pairRowNice W₁') (pairRowNice W₂') + pairRowB3).re ≤ q2word + ½·errKafz·normB`.
  FS correspondence (FINDING §13.2/§13.9): block I ↔ T1, block II ↔ T4, block III ↔ T3, T2 free
  slack; `K1lim ℓ W = Q M_W Q`, `chiChiPart = wLoc`.

The three inputs of the assembly are

* **(S2)** `Work.BoseBoxFock.pairRowS2Bound` — **PROVED** (the `K1exp → K1lim` substitution);
* **images** `Work.BoseBoxFock.stripImages_cost_le` — **PROVED** (`K1lim → pairRowNice`);
* **(S3)** `Work.BoseBoxFock.pairRowS3Bound` — open;
* arithmetic `(re a) ≤ (re b) + ‖a − b‖`, `pairRow_errKafz_add`, `ε₀ := min ε₀₂ (min ε₀₃ ε₀₄)`,
  `Nmin := max Nmin₂ Nmin₃`, `C := C₂ + C₄ + C₃`.

(S3)'s step 1 is `Work.BoseBoxFock.rowShape_aPCgen` (PROVED; `K` arbitrary), its θ-part
`Work.BoseBoxFock.rowShape_thetaPart_eval` (PROVED).  ⚠ The `Σ_k|pinQ_k⟩⟨pinQ_k| = Q` claim of
sessions 6–8 is *unchecked* (FINDING §13.7); the (S2b) budget should be spent on the truncated
kernel `K1exp(1)` directly.

Target: `∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ PotPairRows v h fc fu R J Nmin ε₀ C`
(FS `Q₂` = `(W₁+W₁ω)a₀†a_k†a_ka₀` + Bogoliubov + `(L₀+L₁)∘Σ_k a_k†a_k`, compared with
`q2word` = FS `eq:DefQ2`, up to `½·errKafz·‖Φ‖²`).

`Nmin` is quantified *before* the mode family, so it is ours to choose (the `∀Nmin` form is the
refuted one, `FINDING_PotChiLin_holds_FALSE.md`).  The state and route are recorded in
**`FINDING_PotPairRows_exists.md`** (read §SESSION 3 for the import-cone survey, the truncation
mechanism `Σ_{k∈tail}‖Ŵ(k)‖² → 0`, and the work list).

Proved infrastructure already wired here:

* `Work.BoseBoxFock.potPairRows_pairSet` (`PotPairRowsAux.lean`) — the slot (`pairSet`)
  decomposition of the row: each of the two differences `B(T₁)∘B(T₂) − B(T₁∘T₂)` becomes an
  explicit two-slot `pairSet` sum;
* `Work.BoseBoxFock.pairDecompPairSetGen`, `Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_gen` — the
  slot algebra and the triple-integral evaluation of a two-slot pairing;
* `Work.BoseBoxFock.potPairRows_pairSet_flat`, **`Work.BoseBoxFock.potPairRows_cIPn_pinned_gen`**
  (`PotPairRowsNormalForm.lean`) — the row (with the third block refined into its `pairSet` and
  diagonal parts) in **pinned normal form**: a `pairSet` sum of triple integrals against arbitrary
  a.e.-equal pinned representatives `Fp k =ᵐ η_{f k}`, `Th =ᵐ η_{evec0}`;
* **`Work.BoseBoxFock.potPairRows_cIPn_honest`** (`PotPairRowsHonest.lean`) — the same at the
  honest data (`pinQ v μ HM.N k`, `pinCond v μ c`), via `pinQ_etaOf`,
  `etaOf_evec0_eq_pinCond` and `HonestModes.hf0`.

The remaining steps (FINDING §SESSION 4, §3):

1. the **kernel form** — the finite `Σ_k` moved inside the `x,y,u`-integrals
   (`Work.BoseBoxFock.potPairRows_kernelForm`, PROVED session 4);
2. the **crux** — identify the `qVec` kernel `Σ_k Ŵ(k)qVec k(w)conj(qVec k y)` with
   `ℓ³χ_Λ(w)W₁(w−y)χ_Λ(y)` (plus the `θ`-layer and the images/truncation errors).  The pointwise
   Poisson identity `qVecFrame_kernel` holds only for `W ∈ C^∞_c`, while the honest weight is
   merely bounded with compact support, so the valid statement is the **`L²` convergence of the
   truncated lattice Fourier series to the periodisation**
   (`Work.BoseBoxFock.latFourier_tendsto_periodisation`, **PROVED** session 5);
3. the matching with `q2word` (its `T1..T4` split) and the `errKafz` arithmetic
   (`errKafz` linear in `C`, `Adm_mono`, `n ≤ 2μℓ³`, `n₊ ≤ 𝓜·normB`, `Nmin μ` from the `ℓ²`-tail,
   `ε₀` from `R ≤ ℓ·chiR0`).

### The reduction of the kernel to the four lattice sums (session 5)

`Work.BoseBoxFock.qVec_expansion_finset` (PROVED) splits `Σ_k ρ_k·qVec_k(w)conj(qVec_k y)` on a
**finite** index set into the four sums

    χ(w)χ(y)·Σρ e^{i⟪κ,w−y⟫} − χ(w)θ(y)·Σρ χ̂(ℓκ)e^{i⟪κ,w⟫}
      − θ(w)χ(y)·Σρ χ̂(ℓκ)e^{−i⟪κ,y⟫} + θ(w)θ(y)·Σρ χ̂(ℓκ)² .

With `ρ_k = chat W(kmomLab ℓ N k)` (times the UV cut) and `κ_k = kmomLab ℓ N k`:

* the first sum is the **truncated lattice Fourier series**, whose `L²` limit is the
  periodisation `ℓ³Σ_m W(·+ℓ•latVec m)` (`latFourier_tendsto_periodisation`); the truncation tail
  is `Σ_{k∉Lab N}|chat W(k)|²` (`latTail_cube_le`);
* the three `χ̂`-sums are **absolutely** convergent (`Σ_k|chat W(k)|·|χ̂(ℓk)|^r < ∞`, `χ` is `C^∞`
  with compact support), so their limits are the honest functions
  `Σ_k chat W(k)χ̂(ℓk)^r e^{±i⟪k,·⟫}` and the tails are uniform in the position variable
  (`hatChi_lattice_tail_le`); `latticePoisson_kernel` (PROVED) rewrites them as
  `Σ_m (W ⋆ χ_Λ)(·+ℓm)` once `W` is smooth (the honest `W₁` is not, so the closed form enters
  only at the word-matching stage).

The transferred `L²` statement over the centred box `boxL ℓ = acube ℓ` uses
`latTransfer_integral` (a periodic function has the same integral over both fundamental domains)
and `latFinset_parseval_box` (finite lattice Parseval on the box).

### Session 6: step (S2) is fully reduced, and the *one* remaining analytic input is named

Everything of (S2) except one statement is now verified payable; read
**`FINDING_PotPairRows_exists.md` §SESSION 6** (in particular §6.1 and §6.2) before touching the
error estimates.  In brief:

* the kernel error of blocks **I and II** is an `L²` statement about the periodisation, and every
  ingredient is PROVED (`latRowSum_tendsto_L2`, `latCubeSum_tendsto_L2`, `hatChi_lattice_tail_le`,
  `periodic_double_integral_le`, `kernelImage_le`); the row-level plumbing (writing a triple
  integral as `∫_w∫_y K(w,y)·G(w,y)`) is the fibre layer `Work.BoseBoxFock.integral_fibre`,
  `Work.BoseBoxFock.integral_fibre_two` and **`Work.BoseBoxFock.fibre_kernel_two`**;
* block **III** (weight the constant `1`, so `K1exp(1)` has *no* function limit) is
  `(c₁·n₀ − c₂)·dΓ(S_N)` with `S_N = Σ_{k∈Lab N} rankOne (f k)`, and its limit one-slot kernel
  `Σ_i Q_i χ_Λ² Q_i` is matched by the word's `−μΣ_i Q_i w₁Fibre Q_i` via the PROVED
  `wLoc_fibre_kernelCompare`; the matrix bound `S_N ≤ K(I − E₀₀)` (`Work.BoseBoxFock.frameMat_le`)
  gives `dΓ(S_N) ≤ K·n₊`;
* **the single open analytic input** is the frequency statement
  `dΓ(M − S_N) ≤ ε·‖Φ‖²` (equivalently: the occupation of the `qVec`-modes with
  `‖κ_k‖ > 2πN/ℓ` is small for low-energy states) — it is *not* implied by `SpectralNPlusLe`
  nor by `cnPlus_le_window_of_low`, and it is the only place where the state enters the
  *truncation* error.  See §6.2 `(R3)`.

### ⚠ SESSION 10 (read `FINDING_PotPairRows_exists.md` §10 — this supersedes `D1`/`D2` of §9.16)

The (S2) substitution is run in the **`BoxSmooth` (Dirichlet) interface** of
`Work.BoseBoxFock.pairRowDirDefs`, because the *fibres* of the row are **not** smooth at the honest
data (the state factor is `boxRestrictC ℓ Φ = Φ·1_{abox}` and the condensate pin is
`pinCond = c·1_{boxL}`), while both proved tails (`L1Tails.kernelTail`, T6;
`L1Tails.chiChiImages_pairing_coul`, T7) are stated for a *smooth* test function:

* `BoxSmooth ℓ G` = "`G` agrees on the box squared with a `C^∞` function", with the transport lemmas
  `pairEnergy_congr_box`, `massBox_congr_box`, `setIntegral_pairing_congr_box`;
* `CutSmooth`/`CutSmooth1` + `cutSmooth1_pinCond` (the state pins) and **`boxSmooth_fibres`**
  (PROVED: `pairG13/pairG23/pairG21` are `BoxSmooth` whenever the pins are), which is what makes the
  honest fibres admissible;
* `int_pairing_sub_le_dir` (`pairRowKsubDir`) transfers the *generic* `BoxSmooth` pairing bound to
  the fibre pairing, and `rowPairSubC_Ksub_of_shapes_pair` is the per-pair row assembly;
* `block13/blockTwo3/blockII1_KsubDir` + `rowPairSubC_KsubDir` (`pairRowS2Dir`) are the block- and
  row-level bounds in that interface;
* the pairing bound itself is `Work.BoseBoxFock.K1exp_sub_K1lim_pairing_dirB`
  (`BoseBoxFock/K1exp_sub_K1lim_pairing_dirB.lean`, delegated): `∀ε>0 ∃N₀ ∀N≥N₀ ∀ BoxSmooth G`,
  `‖∫_{box²}(K1exp − K1lim)·G‖ ≤ ε(√(pairEnergy ℓ G) + √(massBox ℓ G))`.  **Both terms are needed**:
  the `θ_Λθ_Λ`-row of `K1exp − K1lim` is the *constant* `ℓ⁻³(pinQD(c) − pinQDl)` times the sharp box
  indicators, so on the box *corners* (`χ_ℓ = 0`, `θ_Λ = 1`) `pairEnergy` alone cannot control it
  (the Dirichlet-only version was refuted by its prover, §10.6 of the FINDING).

### ⚠ SESSION 9 (read `FINDING_PotPairRows_exists.md` §9 — this supersedes the route claims of §8)

* the whole (S2) chain above is stated for **bounded** weights (`∃C, ∀x, ‖W x‖ ≤ C`) and uses the
  boundedness essentially (`Σ_{k∈ℤ³}‖chat W k‖² < ∞`, `latPer_bdd`).  The node's hypotheses give
  only `hv1 : MemLp v 1`, and `W1fun ≤ᵃᵉ 3g₀ ≤ᵃᵉ 3v`, so **`W1fun` need not be bounded nor in
  `L²`**; the (S2) step is therefore **not instantiable at the honest weights as recorded**.  The
  `χ`-row (PROVED) does not suffer from this: `kernelData` uses only `L¹`-data;
* the common missing input for *both* the (S2) tails and the block-III truncation is the **one-body
  (SPECT)** comparison `Σ_{k}τ(κ_k)|⟨qVec_k,u⟩|² ≤ C·⟨u,Tu⟩` (equivalently
  `Σ_{k∈ℤ³}τ(κ_k)⟨Φ,N_kΦ⟩ ≤ C·kinFormB Φ`), together with
  `kinFormB ≤ 12πaμ²ℓ³‖Φ‖²` (elementary, §9.3).  With it, `Nmin μ ~ (μa³)^{-1/4}`-scale makes every
  omitted-mode tail `≤ ε‖Φ‖²` uniformly in the state.

### ⚠ SESSION 11 (read `FINDING_PotPairRows_exists.md` §SESSION 11 — it supersedes the (S2) *error*
### claim of §10.13)

The honest dictionary and the row identity are now PROVED (`pairRowHonestRed`: `E.W1 = k1cfun fu
W1fun 0`, `E.W1 + E.W1ω = k1cfun fu W1fun W1omegaFun`, `cIPn_potPairRows_eq`), and the régime
lemmas the (S2) instantiation needs are landed (`W1fun_integrable_of_regime`,
`W1omega_weight_facts`, `exists_threshold_sideAt_ge_mul`, `rowSum_roots_le_const`).

**But the (S2) error estimate CANNOT be closed through the unweighted `pinDir`**: `pairEnergy` is
`χ_ℓ`-*weighted* in its first variable, while `pairG_dir_leB`/`rowSum_roots_le` route it through the
unweighted state content `pinDir`, which the node's hypotheses do **not** bound (a smooth state
concentrated in a *corner* of the box cube has `wLoc ≡ 0`, `fsT`'s words vanishing to `O(1/ℓ²)`,
hence `IsLowB` and `SpectralNPlusLe`, while `pinDir/normB ≍ 1/δ² → ∞`).  The node remains TRUE (the
corner family satisfies it with a large margin) — the fix is the **`χ`-weighted** state content
`pinDirChi` (`pairRowDirChi`) together with the weighted twins of `pairG_dir_leB` and of the slice
identities, and with `pinDirChi ≤ C·(kinFormB + n·normB)` (via `bsOneBody_eq_dirichlet`,
`bsOneBody_fsKinCoeff_ge_mass`, and `mainWord = (1-εT)bsOneBody(χ·Qψ) + …`).

Still open: **(S2b)** block III (no function kernel limit for the constant-weight sum) and **(S3)**
(the dictionary `rowPairSubC (K1lim W₁′) (K1lim W₂′) + III ≤ q2word + err`).  Both are independent
of the weighting issue.

### ⚠ SESSION 12 (`FINDING_PotPairRows_exists.md` §SESSION 12) — **(S2) IS COMPLETE**, and the (S3)
### dictionary is structurally understood as `K1lim ℓ W = Q·(χχ-periodisation)·Q`

The whole (S2) error half is now a **proved interface** (all `sorry`-free, axiom-clean, imported
above): `pairG_dir_leB_chi` + `pairDirChi_slices` (the χ-weighted fibre estimates),
`rowSum_roots_le_chi` (the `n`-free row-sum bound with `pinDir → pinDirChi`),
`pinDirChi_le_kinFormB` (the state content ≤ `C(kinFormB + n·normB)`),
`pairRowS2Arith` (the μ-only arithmetic), and — composing the last two with the PROVED
`rowPairSubC_stateDir` — **`rowPairSubC_stateDir_le`**:
`‖rowPairSubC (ℓ³)⁻¹ Θ A KI KII − rowPairSubC (ℓ³)⁻¹ Θ A (K1lim ℓ W₁') (K1lim ℓ W₂')‖ ≤
2ℓ⁻³ max ε₁ε₂ · Cf ℓ n² (cA²√pL√(pinDirChi+pL) + A₂L₂)`.
The only remaining (S2) work is the **instantiation at the honest data** (plumbing over
`K1exp_meas_bdd`, `pinCond_measurable`/`pinCond_bdd`/`pinCond_norm_sq`, `cutSmooth1_pinCond`,
`W1fun_integrable_of_regime`, `W1omega_weight_facts`, `kinFormBLeLowBudgetB`,
`K1exp_sub_K1lim_pairing_dirB`, `errKafz_ge_slot`, `boxRestrictState`) — recipe in FINDING §12.1.

For **(S3)**: `pairRowS3Split.lean` splits the honest limit kernel as
`K1lim = chiChiPart + chiChiImages + thetaPart`, `chiChiPart ℓ (wScaled ℓ h) = wLoc ℓ h 0`,
`thetaPart` = the three `χ̂`-rows.  The structural point (FINDING §12.2): writing
`Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|` and `modeVec_k = χ_Λe^{i⟪κ_k,·⟫}`, one has **`K1lim ℓ W = Q·M_W·Q`** with
`M_W(w,z) = χ_Λ(w)Σ_m W(w−z+ℓm)χ_Λ(z)`; hence the row's slots are literally the word's `aP`/`aQ`
slots (`A(x p.1) = c` on the support, `∫_u θ_Λ(u)Θ(x[p.1↦y][p.2↦u])du = ℓ³aPC ℓ p.2 Θ(x[p.1↦y])`
— the PROVED `setIntegral_thetaFun_mul_update`), and the `m = 0` part of `M_W` is the word's kernel
`wLoc`.  So (S3) is an *exact algebraic comparison*; the work list (steps 1–4, including the (S2b)
high-mode tail `Γ(Q − S_N) ≤ ε·normB` via T2′/`highModeTail` + the session-12 one-body chain) is
FINDING §12.4.
-/

namespace Work.BoseBoxFock

theorem PotPairRows_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.PotPairRows v h fc fu R J Nmin ε₀ C :=
  PotPairRows_exists_assembly v h hv hv1 hvrad hR hv_supp hav fc fu J hB3

end Work.BoseBoxFock
