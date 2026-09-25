/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-step Bochner–Martinelli defect gains one derivative (smooth cut-off)

`Work.NN.Core.bmDefect_gain` proves the one-derivative gain for the defect of a single
Bochner–Martinelli step, but assumes the cut-off `χ` to be *analytic* (`ContDiff ℝ ⊤ χ`).
The assembly of the `(0,2)`-solver only has a *smooth* cut-off (`ContDiff ℝ ∞ χ`,
`∞ = ↑(⊤ : ℕ∞)`) at its disposal, so this file reproves the statement with the smooth
hypothesis — the form in which the estimate is actually used.

The only place where analyticity of `χ` enters `bmDefect_gain` is the Schauder input
`Work.NN.Core.holderNorm_bmH_le_uniform`, i.e. the estimate of the components of the
algebraic form `bmH χ ζ` in `C^{k,α}(ℂⁿ)` by `Σ ‖ζ‖_{C^{k,α}(polydisc 0 ρ)}`, with a constant
uniform in `ζ`.  Here that input is replaced by the `C^{k+1}`-multiplier bound
`TelTwoDF.holderNorm_bump_mul_le`, applied to the three products `∂̄_a χ · ζ_{rs}` out of
which `bmH` is built: `∂̄_a χ` is smooth (hence `C^{k+1}`) with compact support contained in
`tsupport χ ⊆ polydisc 0 ρ` and it vanishes on the closed exterior of `polydisc 0 ρ`, which is
exactly what that lemma needs.

## Main results

* `holderNorm_bmH_le_of_smooth` — the uniform (in `ζ`) `C^{k,α}` bound for `bmH χ ζ`.
* `bmDefect_gain_smooth` — the gain estimate for the smooth cut-off.
-/
import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.NN.Core.bmDefect_gain
import Submission.Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le
import Submission.Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset

namespace Work.NN.Core

open scoped NNReal ENNReal Topology ContDiff
open Set Filter
open Work.CR.Flat

noncomputable section

variable {n : ℕ}

/-! ## Regularity, support and vanishing of `∂̄ χ` for a smooth `χ` -/

/-- `∂̄_j χ` is smooth whenever `χ` is. -/
lemma contDiff_dbarCoord_of_smooth {j : Fin n} {χ : Cn n → ℂ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => dbarCoord j χ z) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ χ) :=
    (contDiff_infty_iff_fderiv.mp hχ).2
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ χ z (Pi.single j (1 : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ χ z (Pi.single j (Complex.I : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (1 / 2 : ℂ) * (fderiv ℝ χ z (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ χ z (Pi.single j (Complex.I : ℂ)))) :=
    contDiff_const.mul (h1.add (contDiff_const.mul h2))
  simpa only [dbarCoord] using h3

/-- `∂̄_a χ` vanishes at every point outside the topological support of `χ`. -/
lemma dbarCoord_eq_zero_of_notMem_tsupport {χ : Cn n → ℂ} {w : Cn n} (hw : w ∉ tsupport χ)
    (a : Fin n) : dbarCoord a χ w = 0 := by
  have hn : (tsupport χ)ᶜ ∈ nhds w := (isClosed_tsupport χ).isOpen_compl.mem_nhds hw
  have heq : χ =ᶠ[nhds w] (fun _ : Cn n => 0) := by
    filter_upwards [hn] with y hy
    by_contra hy'
    exact hy (subset_tsupport χ (Function.mem_support.mpr hy'))
  have hfd : fderiv ℝ χ w = 0 := by
    rw [heq.fderiv_eq, fderiv_const_apply]
  simp [dbarCoord, hfd]

/-- The topological support of `∂̄_a χ` is contained in that of `χ`. -/
lemma tsupport_dbarCoord_subset {χ : Cn n → ℂ} (a : Fin n) :
    tsupport (fun z => dbarCoord a χ z) ⊆ tsupport χ := by
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport χ)
  intro z hz
  by_contra hzc
  exact hz (dbarCoord_eq_zero_of_notMem_tsupport hzc a)

/-- `∂̄_a χ` is compactly supported when `χ` is. -/
lemma hasCompactSupport_dbarCoord {χ : Cn n → ℂ} (hcs : HasCompactSupport χ) (a : Fin n) :
    HasCompactSupport (fun z => dbarCoord a χ z) := by
  rw [HasCompactSupport] at hcs ⊢
  exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) (tsupport_dbarCoord_subset a)

/-! ## The uniform `C^{k,α}` bound for the components of `bmH` -/

/-- **The components of `bmH χ ζ` are bounded in `C^{k,α}(ℂⁿ)` by `Σ ‖ζ‖_{C^{k,α}(polydisc 0 ρ)}`,
with a constant independent of `ζ`.**

The three products `∂̄_a χ · ζ_{rs}` are each multiplied by a smooth compactly supported
`∂̄_a χ` vanishing on the closed exterior of the polydisc, so `holderNorm_bump_mul_le` gives a
bound by `‖ζ_{rs}‖_{C^{k,α}(polydisc 0 ρ)}` with a constant depending on `∂̄_a χ` only; `bmH` is
the sum/difference of the three products. -/
lemma holderNorm_bmH_le_of_smooth {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {k : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {χ : Cn n → ℂ}
    (hsm : ∀ a : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => dbarCoord a χ z))
    (hcs : ∀ a : Fin n, HasCompactSupport (fun z => dbarCoord a χ z))
    (hvan : ∀ (a : Fin n) z, (∃ j, ρ j ≤ ‖z j‖) → dbarCoord a χ z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Fin n → Fin n → Cn n → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (ζ i l) (polydisc 0 ρ)) →
      (∀ i l, holderNorm k α (ζ i l) (polydisc 0 ρ) ≠ ⊤) →
      ∀ j m : Fin n,
        (∑ l : Fin n, holderNorm k α (bmH χ ζ j m l) Set.univ)
          ≤ ENNReal.ofReal C * ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) := by
  classical
  -- one multiplication constant per `∂̄_a χ`
  have hconst : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧ ∀ u : Cn n → ℂ,
      ContDiffOn ℝ (k : ℕ∞) u (polydisc 0 ρ) →
      holderNorm k α (fun z => dbarCoord a χ z * u z) Set.univ
        ≤ ENNReal.ofReal Ca * holderNorm k α u (polydisc 0 ρ) := by
    intro a
    exact TelTwoDF.holderNorm_bump_mul_le hα0 hα1 k hρ (fun z => dbarCoord a χ z)
      ((hsm a).of_le (by simp)) (hcs a) (hvan a)
  choose Ca hCapos hCa using hconst
  set C3 : ℝ := 1 + ∑ a : Fin n, Ca a with hC3def
  have hC3pos : 0 < C3 := by
    rw [hC3def]
    have h0 : (0 : ℝ) ≤ ∑ a : Fin n, Ca a := Finset.sum_nonneg (fun a _ => (hCapos a).le)
    linarith
  have hCa_le : ∀ a : Fin n, Ca a ≤ C3 := by
    intro a
    rw [hC3def]
    have h1 : Ca a ≤ ∑ a : Fin n, Ca a :=
      Finset.single_le_sum (f := fun a : Fin n => Ca a) (fun a _ => (hCapos a).le)
        (Finset.mem_univ a)
    linarith
  refine ⟨(n : ℝ) * (3 * C3) + 1, by positivity, ?_⟩
  intro ζ hζ hζfin j m
  set M : ℝ≥0∞ := ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) with hMdef
  -- each individual norm is at most `M`
  have hS1 : ∀ i : Fin n, (∑ l : Fin n, holderNorm k α (ζ i l) (polydisc 0 ρ)) ≤ M :=
    fun i => by
      rw [hMdef]
      exact Finset.single_le_sum (f := fun i => ∑ l : Fin n,
        holderNorm k α (ζ i l) (polydisc 0 ρ)) (fun _ _ => bot_le) (Finset.mem_univ i)
  have hS2 : ∀ i l : Fin n, holderNorm k α (ζ i l) (polydisc 0 ρ) ≤ M := fun i l =>
    (Finset.single_le_sum (f := fun l => holderNorm k α (ζ i l) (polydisc 0 ρ))
      (fun _ _ => bot_le) (Finset.mem_univ l)).trans (hS1 i)
  -- the bound for each individual product `∂̄_a χ · ζ_{rs}`
  have hprod : ∀ (a r s : Fin n),
      holderNorm k α (fun z => dbarCoord a χ z * ζ r s z) Set.univ ≤ ENNReal.ofReal C3 * M := by
    intro a r s
    refine (hCa a (ζ r s) ((hζ r s).of_le (by exact_mod_cast Nat.le_succ k))).trans ?_
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hCa_le a)) _).trans
      (mul_le_mul_right (hS2 r s) _)
  -- the bound for one component of `bmH`
  have hbmH : ∀ l : Fin n,
      holderNorm k α (bmH χ ζ j m l) Set.univ ≤ ENNReal.ofReal (3 * C3) * M := by
    intro l
    have hA := hprod l j m
    have hB := hprod j m l
    have hC := hprod m j l
    have hcdA : ContDiffOn ℝ (k : ℕ∞) (fun z => dbarCoord l χ z * ζ j m z) Set.univ :=
      (contDiff_flatMul_of_smooth hρ (hsm l) (hvan l) (hζ j m) (hζfin j m)).contDiffOn
    have hcdB : ContDiffOn ℝ (k : ℕ∞) (fun z => dbarCoord j χ z * ζ m l z) Set.univ :=
      (contDiff_flatMul_of_smooth hρ (hsm j) (hvan j) (hζ m l) (hζfin m l)).contDiffOn
    have hcdC : ContDiffOn ℝ (k : ℕ∞) (fun z => dbarCoord m χ z * ζ j l z) Set.univ :=
      (contDiff_flatMul_of_smooth hρ (hsm m) (hvan m) (hζ j l) (hζfin j l)).contDiffOn
    have huniq : UniqueDiffOn ℝ (Set.univ : Set (Cn n)) := isOpen_univ.uniqueDiffOn
    have hsplit : bmH χ ζ j m l
        = fun z => (dbarCoord l χ z * ζ j m z + dbarCoord j χ z * ζ m l z)
            + (-1 : ℂ) * (dbarCoord m χ z * ζ j l z) := by
      funext z
      simp only [bmH]
      ring
    rw [hsplit]
    calc holderNorm k α (fun z => (dbarCoord l χ z * ζ j m z + dbarCoord j χ z * ζ m l z)
            + (-1 : ℂ) * (dbarCoord m χ z * ζ j l z)) Set.univ
        ≤ holderNorm k α (fun z => dbarCoord l χ z * ζ j m z + dbarCoord j χ z * ζ m l z)
              Set.univ
            + holderNorm k α (fun z => (-1 : ℂ) * (dbarCoord m χ z * ζ j l z)) Set.univ :=
          Work.CR.Flat.Holder.holderNorm_add_le (hcdA.add hcdB) (contDiffOn_const.mul hcdC) huniq
      _ ≤ (holderNorm k α (fun z => dbarCoord l χ z * ζ j m z) Set.univ
              + holderNorm k α (fun z => dbarCoord j χ z * ζ m l z) Set.univ)
            + ENNReal.ofReal ‖(-1 : ℂ)‖
              * holderNorm k α (fun z => dbarCoord m χ z * ζ j l z) Set.univ :=
          add_le_add (Work.CR.Flat.Holder.holderNorm_add_le hcdA hcdB huniq)
            (holderNorm_const_mul_le huniq (-1) _)
      _ ≤ (ENNReal.ofReal C3 * M + ENNReal.ofReal C3 * M) + ENNReal.ofReal C3 * M := by
          refine add_le_add (add_le_add hA hB) ?_
          have h1 : ENNReal.ofReal ‖(-1 : ℂ)‖ = 1 := by simp
          rw [h1, one_mul]
          exact hC
      _ = ENNReal.ofReal (3 * C3) * M := by
          have h3 : ENNReal.ofReal (3 * C3)
              = ENNReal.ofReal C3 + ENNReal.ofReal C3 + ENNReal.ofReal C3 := by
            rw [show (3 : ℝ) * C3 = C3 + C3 + C3 by ring,
              ENNReal.ofReal_add (by linarith) (by linarith),
              ENNReal.ofReal_add hC3pos.le hC3pos.le]
          rw [h3, add_mul, add_mul]
  calc ∑ l : Fin n, holderNorm k α (bmH χ ζ j m l) Set.univ
      ≤ ∑ _l : Fin n, ENNReal.ofReal (3 * C3) * M := Finset.sum_le_sum fun l _ => hbmH l
    _ = (n : ℝ≥0∞) * (ENNReal.ofReal (3 * C3) * M) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((n : ℝ) * (3 * C3)) * M := by
        rw [← ENNReal.ofReal_natCast n, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((n : ℝ) * (3 * C3) + 1) * M :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (by linarith [hC3pos, Nat.cast_nonneg (α := ℝ) n])) M

/-! ## The gain estimate -/

theorem bmDefect_gain_smooth {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχcs : HasCompactSupport χ) (hχts : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ)
    (hχone : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ' → χ z = 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (ζ i l) (Work.CR.Flat.polydisc 0 ρ)) →
      ∀ j m, Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmDefect χ ζ j m)
          (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal C * ∑ i, ∑ l,
            Work.CR.Flat.holderNorm k α (ζ i l) (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  -- `χ` vanishes on the closed exterior of the polydisc
  have hχsub : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    have hzP : z ∉ polydisc 0 ρ := by
      rw [mem_polydisc]
      intro h
      obtain ⟨j, hj⟩ := hz
      exact absurd (h j) (not_lt.mpr (by simpa using hj))
    exact Function.notMem_support.mp fun hmem => hzP (hχts (subset_tsupport χ hmem))
  -- the sums `χ` is cut by
  have hsm : ∀ a : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => dbarCoord a χ z) :=
    fun a => contDiff_dbarCoord_of_smooth hχ
  have hcsd : ∀ a : Fin n, HasCompactSupport (fun z => dbarCoord a χ z) :=
    fun a => hasCompactSupport_dbarCoord hχcs a
  have hvan : ∀ (a : Fin n) z, (∃ j, ρ j ≤ ‖z j‖) → dbarCoord a χ z = 0 :=
    fun a => dbarCoord_eq_zero_of_vanishing_off_polydisc hρ (hχ.of_le (by simp)) hχsub a
  -- the two constants: the uniform `bmH` bound, and the Bochner–Martinelli Schauder estimate
  obtain ⟨CH, hCHpos, hCH⟩ :=
    holderNorm_bmH_le_of_smooth (n := n) (k := k) hα.le (le_of_lt hα1) hρ hsm hcsd hvan
  obtain ⟨CD, hCDpos, hCD⟩ := bmPot_riesz_Ck (n := n) hn (c := 0)
    (r := fun j => 2 * ρ j) hα hα1 (fun j => by linarith [hρ j]) k
  refine ⟨‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * (CH + 1) + 1, by positivity, ?_⟩
  intro ζ hζ j m
  set M : ℝ≥0∞ := ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) with hMdef
  by_cases hMtop : M = ⊤
  · rw [hMtop, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · -- finiteness of the data
    have hζfin : ∀ i l, holderNorm k α (ζ i l) (polydisc 0 ρ) ≠ ⊤ := by
      intro i l
      refine ne_top_of_le_ne_top hMtop ?_
      rw [hMdef]
      exact le_trans
        (Finset.single_le_sum (f := fun l' => holderNorm k α (ζ i l') (polydisc 0 ρ))
          (fun l' _ => bot_le) (Finset.mem_univ l))
        (Finset.single_le_sum (f := fun i' => ∑ l',
            holderNorm k α (ζ i' l') (polydisc 0 ρ))
          (fun i' _ => bot_le) (Finset.mem_univ i))
    -- the uniform bound on the components of `bmH`
    have hsumH : (∑ l : Fin n, holderNorm k α (bmH χ ζ j m l) Set.univ)
        ≤ ENNReal.ofReal CH * M := by
      rw [hMdef]
      exact hCH ζ hζ hζfin j m
    -- hence each component has finite `C^{k,α}` norm on `ℂⁿ`
    have hGfin : ∀ l : Fin n, holderNorm k α (bmH χ ζ j m l) Set.univ < ⊤ := by
      intro l
      have h1 : holderNorm k α (bmH χ ζ j m l) Set.univ ≤ ENNReal.ofReal CH * M :=
        (Finset.single_le_sum
          (f := fun l' => holderNorm k α (bmH χ ζ j m l') Set.univ)
          (fun l' _ => bot_le) (Finset.mem_univ l)).trans hsumH
      exact lt_of_le_of_lt h1
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hMtop))
    -- and it is `C^k` on all of `ℂⁿ`
    have hGcont : ∀ l : Fin n, ContDiff ℝ k (bmH χ ζ j m l) := by
      intro l
      rw [bmH_eq]
      have t1 := contDiff_flatMul_of_smooth hρ (hsm l) (hvan l) (hζ j m) (hζfin j m)
      have t2 := contDiff_flatMul_of_smooth hρ (hsm j) (hvan j) (hζ m l) (hζfin m l)
      have t3 := contDiff_flatMul_of_smooth hρ (hsm m) (hvan m) (hζ j l) (hζfin j l)
      simpa only [Pi.add_apply, Pi.sub_apply] using (t1.add t2).sub t3
    -- and it vanishes off the polydisc of radii `2ρ`
    have hGsupp : ∀ l z, (∃ i, (fun j => 2 * ρ j) i / 2 ≤ ‖z i‖) → bmH χ ζ j m l z = 0 := by
      intro l z hz
      obtain ⟨i, hi⟩ := hz
      have hi' : ρ i ≤ ‖z i‖ := by
        rw [show (fun j => 2 * ρ j) i / 2 = ρ i from by ring] at hi
        exact hi
      simp only [bmH, hvan l z ⟨i, hi'⟩, hvan j z ⟨i, hi'⟩, hvan m z ⟨i, hi'⟩,
        zero_mul, add_zero, sub_zero]
    -- the Schauder estimate for the potential of `bmH`
    have hD := hCD (fun l => bmH χ ζ j m l) hGcont hGfin
      (fun l z hz => hGsupp l z (by simpa using hz))
    rw [← show (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z)
          = Work.CR.Flat.Cauchy.bmPotential (fun l => bmH χ ζ j m l) from
        funext (fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ z).symm)] at hD
    have hpol : polydisc (0 : Cn n) (fun j => 2 * ρ j / 2) = polydisc 0 ρ := by
      congr 1
      funext j
      ring
    rw [hpol] at hD
    have hmono : holderNorm (k + 1) α
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ')
        ≤ holderNorm (k + 1) α
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ) :=
      holderNorm_mono_set (isOpen_polydisc 0 ρ) (isOpen_polydisc 0 ρ')
        (polydisc_mono (fun j => le_of_lt (hlt j))) (k + 1) α _
    have hD' : holderNorm (k + 1) α
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal CD * ∑ l, holderNorm k α (bmH χ ζ j m l) Set.univ :=
      hmono.trans hD
    have hD'' : holderNorm (k + 1) α
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (CD * CH) * M := by
      refine hD'.trans ?_
      calc ENNReal.ofReal CD * ∑ l, holderNorm k α (bmH χ ζ j m l) Set.univ
          ≤ ENNReal.ofReal CD * (ENNReal.ofReal CH * M) := mul_le_mul_right hsumH _
        _ = ENNReal.ofReal (CD * CH) * M := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCDpos.le]
    -- `bmDefect` agrees with `-γ⁻¹ • bmPot(bmH)` on `polydisc 0 ρ'`
    have hcongr : holderNorm (k + 1) α (bmDefect χ ζ j m) (polydisc 0 ρ')
        = holderNorm (k + 1) α
            (fun z => -(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
              * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ') :=
      holderNorm_congr_on fun z hz => by
        rw [bmDefect_apply]
        have h1 : χ z = 1 := hχone z hz
        rw [h1]
        ring
    rw [hcongr]
    -- pull out the constant
    have hscale : holderNorm (k + 1) α
        (fun z => -(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
          * holderNorm (k + 1) α
              (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z)
              (polydisc 0 ρ') := by
      simpa only [norm_neg] using
        (holderNorm_const_mul_le (isOpen_polydisc 0 ρ').uniqueDiffOn
          (-(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)))
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z))
    refine hscale.trans ?_
    calc ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
          * holderNorm (k + 1) α
              (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j m l) z)
              (polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
            * (ENNReal.ofReal (CD * CH) * M) := mul_le_mul_right hD'' _
      _ = ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * (CD * CH)) * M := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * (CH + 1) + 1) * M := by
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) M
            have h1 : (0 : ℝ) ≤ ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD :=
              mul_nonneg (norm_nonneg _) hCDpos.le
            have h2 : (0 : ℝ) ≤ ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * CH := by
              exact mul_nonneg h1 hCHpos.le
            linarith
      _ = ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * (CH + 1) + 1)
            * ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) := by rw [hMdef]

end

end Work.NN.Core
