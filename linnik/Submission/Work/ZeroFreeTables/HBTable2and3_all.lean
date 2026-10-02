import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.RowCert_all
import Submission.Work.ZeroFreeTables.t23certG
import Submission.Work.ZeroFreeTables.t23cover
import Submission.Work.ZeroFreeTables.t23witness
import Submission.Work.ZeroFreeTables.t23glue
import Submission.Work.ZeroFreeTables.t23simple
import Submission.Work.ZeroFreeTables.t23l52
import Submission.Work.ZeroFreeTables.t23lam3
import Submission.Work.ZeroFreeTables.t23lam3num
import Submission.Work.ZeroFreeTables.t23lamsmem
import Submission.Work.ZeroFreeTables.t23pos
import Submission.Work.ZeroFreeTables.t23triBound
import Submission.Work.ZeroFreeTables.t23guard
import Submission.Work.ZeroFreeTables.lam0w.TestFn_E_mono
import Submission.Work.ZeroFreeTables.lam0w.s6_real_low
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.log_unbounded_nat
import Submission.Work.ZeroFreeTables.t23NearLineCountLogFree

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

/-!
# `HBTable2and3_all`: HB's Tables 2 and 3 assembled

The engine statement `Work.ZeroFreeTables.HBTable2and3` (HB's Tables 2 and 3, p. 38, i.e. the
`F`-method of §6 with the optimal test functions of §7 at `k = 2/3`) from the pieces proved in this
workspace:

* `RowCert_all` / `t23certG` — the row certificates (`hb72G`-form),
* `t23cover` — the coverage `RowCover` of the two ranges by the rows,
* `lam0w.TF_eq_hb` — the identification `F_λ(x) = G(-x/λ)/30`,
* `t23glue` — HB Lemma 6.3 in the `F`-language (`GlueH63`),
* `t23l52`, `t23simple` — the `φ = 1/4` log-derivative input and the simplicity of `ρ₁`,
* `t23GlueWitness_of_logFreeCount` + `t23NearLineCountLogFree` — the box witness
  (`GlueWitness`) from the *unconditional* log-free near-line count, and
* `t23lam3` + `t23lam3num` — the fixed-scale (`λ = 3`) failure used for `λ₁ ≤ 10⁻³`.

The mechanism is HB's: for a zero `ρ ≠ ρ₁` of `χ₁` take the witness `ρ'` (a zero of `χ₁` of
minimal `λ` in a box, which exists by `GlueWitness`), apply HB Lemma 6.3 to `ρ'` at the scale of a
row `(λ, b, v)` of Table 2/3 with `λ₁ ≤ b`, and use the failure of the tabulated `F`-expression at
`(v, b)` together with the monotonicity of `E(λ₀,λ₁) = 2(F(−λ₀) − F(λ₁−λ₀))` to conclude
`λ(ρ') ≥ v ≥` the required bound; then `λ(ρ) ≥ λ(ρ')`.
-/

/-! ## The near-line count and the witness -/

/-- The log-free near-line count of a single character (as proved in
`Submission.Work.ZeroFreeTables.t23NearLineCountLogFree`); this is the *hypothesis shape* accepted
by `t23GlueWitness_of_logFreeCount`. -/
def NearLineCountLogFree : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ A < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
      t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
        ≤ C * (Real.log (q : ℝ)) ^ A

theorem t23NearLineCountLogFree_holds : NearLineCountLogFree :=
  t23NearLineCountLogFree

/-! ## Threshold lemmas -/

/-- `K ≤ log q` for all large `q`. -/
private theorem exists_log_ge (K : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → K ≤ Real.log (q : ℝ) :=
  Work.LinnikAreas.log_unbounded_nat K

/-- `K ≤ (1/3) log log log q` for all large `q`. -/
private theorem exists_lamMax_ge (K : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → K ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
  obtain ⟨q₀, hq₀⟩ := Work.LinnikAreas.log_unbounded_nat (Real.exp (Real.exp (3 * K)))
  refine ⟨max q₀ 2, ?_⟩
  intro q hq
  have h1 : Real.exp (Real.exp (3 * K)) ≤ Real.log (q : ℝ) :=
    hq₀ q (le_trans (le_max_left _ _) hq)
  have h2 : Real.exp (3 * K) ≤ Real.log (Real.log (q : ℝ)) := by
    have h3 := Real.log_le_log (Real.exp_pos (Real.exp (3 * K))) h1
    rwa [Real.log_exp] at h3
  have h4 : 3 * K ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h5 := Real.log_le_log (Real.exp_pos (3 * K)) h2
    rwa [Real.log_exp] at h5
  linarith

/-- `6 ≤ log 1000`. -/
private theorem six_le_log_thousand : (6 : ℝ) ≤ Real.log 1000 := by
  have h10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)]
    have h := Real.exp_one_lt_three
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h3 : Real.exp 2 < 10 := by rw [h2]; nlinarith [Real.exp_pos 1, h]
    linarith
  have h3 : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- `log (1/λ) ≥ log 1000` for `0 < λ ≤ 1/1000`. -/
private theorem log_thousand_le {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 1000) :
    Real.log 1000 ≤ Real.log (1 / lam) := by
  refine Real.log_le_log (by norm_num) ?_
  rw [le_div_iff₀ h0]
  linarith

/-- `1.294 ≤ (3/2) log (1/λ)` for `0 < λ ≤ 1/1000`. -/
private theorem one_two_nine_four_le {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 1000) :
    (1294 / 1000 : ℝ) ≤ (3 / 2) * Real.log (1 / lam) := by
  have hlog := log_thousand_le h0 h1
  have h1000 := six_le_log_thousand
  linarith

/-- `4 ≤ min (4 e) (2 log (1/λ))` for `0 < λ ≤ 1/1000`. -/
private theorem four_le_min {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 1000) :
    (4 : ℝ) ≤ min (4 * Real.exp 1) (2 * Real.log (1 / lam)) := by
  have hlog := log_thousand_le h0 h1
  have h1000 := six_le_log_thousand
  have hexp := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  refine le_min ?_ ?_
  · linarith
  · linarith

/-! ## The row mechanism -/

/-- **The §6 inequality in `hb72G` language.**  The `F`-form of HB Lemma 6.3 at the test function
of scale `lam` is the `hb72G`-form of the row certificates. -/
theorem hb63_G {q : ℕ} [NeZero q] {ρ₁ ρ' : ℂ} {lam : ℝ}
    (hlam : 0 < lam)
    (h : 0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ'))
      - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
      - (tf72T lam hlam).F 0 + (tf72T lam hlam).f 0 * CertSlack) :
    8 / 9 - CertSlack * (16 * lam / 15)
      ≤ (1 / 15) * (hb72G (lamOf q ρ' / lam) - hb72G ((lamOf q ρ' - lamOf q ρ₁) / lam)) := by
  have e1 : (tf72T lam hlam).F (-(lamOf q ρ')) = hb72G (lamOf q ρ' / lam) / 30 := by
    rw [lam0w.TF_eq_hb lam hlam (-(lamOf q ρ')), neg_neg]
  have e2 : (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
      = hb72G ((lamOf q ρ' - lamOf q ρ₁) / lam) / 30 := by
    rw [lam0w.TF_eq_hb lam hlam (lamOf q ρ₁ - lamOf q ρ'),
      show -(lamOf q ρ₁ - lamOf q ρ') / lam = (lamOf q ρ' - lamOf q ρ₁) / lam by ring]
  have e3 : (tf72T lam hlam).F 0 = 8 / 9 := lam0w.TF_zero lam hlam
  have e4 : (tf72T lam hlam).f 0 = 16 * lam / 15 := lam0w.TF_f0 lam hlam
  rw [e1, e2, e3, e4] at h
  have h' : 8 / 9 - CertSlack * (16 * lam / 15)
      ≤ 2 * (hb72G (lamOf q ρ' / lam) / 30 - hb72G ((lamOf q ρ' - lamOf q ρ₁) / lam) / 30) := by
    linarith
  calc 8 / 9 - CertSlack * (16 * lam / 15)
      ≤ 2 * (hb72G (lamOf q ρ' / lam) / 30 - hb72G ((lamOf q ρ' - lamOf q ρ₁) / lam) / 30) := h'
    _ = (1 / 15) * (hb72G (lamOf q ρ' / lam) - hb72G ((lamOf q ρ' - lamOf q ρ₁) / lam)) := by
        ring

/-- **The row certificate in the `F`-language.** -/
theorem F_of_cert {lam b v : ℝ} (hlam : 0 < lam)
    (hcert : (1 / 15) * (hb72G (v / lam) - hb72G ((v - b) / lam))
      < 8 / 9 - CertSlack * (16 * lam / 15)) :
    2 * ((tf72T lam hlam).F (-v) - (tf72T lam hlam).F (b - v))
      < (tf72T lam hlam).F 0 - (tf72T lam hlam).f 0 * CertSlack := by
  have e1 : (tf72T lam hlam).F (-v) = hb72G (v / lam) / 30 := by
    rw [lam0w.TF_eq_hb lam hlam (-v), neg_neg]
  have e2 : (tf72T lam hlam).F (b - v) = hb72G ((v - b) / lam) / 30 := by
    rw [lam0w.TF_eq_hb lam hlam (b - v),
      show -(b - v) / lam = (v - b) / lam by ring]
  have e3 : (tf72T lam hlam).F 0 = 8 / 9 := lam0w.TF_zero lam hlam
  have e4 : (tf72T lam hlam).f 0 = 16 * lam / 15 := lam0w.TF_f0 lam hlam
  rw [e1, e2, e3, e4]
  linarith

/-- **The row mechanism.**  If the §6 inequality of HB Lemma 6.3 holds at the test zero `ρ'` (in
the `F`-language of `GlueH63`), the row certificate of `(lam, b, v)` fails at `(v, b)`, and
`λ(ρ₁) ≤ b`, then `λ(ρ') ≥ v`. -/
theorem row_bound₀ {q : ℕ} [NeZero q] {ρ₁ ρ' : ℂ}
    {lam b v : ℝ} (hlam : 0 < lam)
    (h : 0 ≤ 2 * (tf72T lam hlam).F (-(lamOf q ρ'))
      - 2 * (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')
      - (tf72T lam hlam).F 0 + (tf72T lam hlam).f 0 * CertSlack)
    (hcert : (1 / 15) * (hb72G (v / lam) - hb72G ((v - b) / lam))
      < 8 / 9 - CertSlack * (16 * lam / 15))
    (hb : lamOf q ρ₁ ≤ b) (h1 : 0 ≤ lamOf q ρ₁) :
    v ≤ lamOf q ρ' := by
  have hF := F_of_cert hlam hcert
  have hineq : (tf72T lam hlam).F 0 - (tf72T lam hlam).f 0 * CertSlack
      ≤ 2 * ((tf72T lam hlam).F (-(lamOf q ρ'))
        - (tf72T lam hlam).F (lamOf q ρ₁ - lamOf q ρ')) := by
    linarith
  by_contra hcon
  push_neg at hcon
  have hmono := lam0w.TestFn_E_mono (tf72T lam hlam) hcon.le hb h1
  linarith

/-! ## The first conjunct of `HBTable2and3` -/

/-- **HB Table 2** (the first conjunct of `HBTable2and3`): for `λ₁ ≤ 1/5` every other zero of `χ₁`
in the working region has `λ ≥ min (4e) ((2-ε) log (1/λ₁))`. -/
theorem hb23_conj1 (hcount : NearLineCountLogFree) (ε : ℝ) (hε : 0 < ε)
    (lamS : ℝ) (hlamS : 0 < lamS) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS ≤ lamOf q ρ₁ →
      lamOf q ρ₁ ≤ 1 / 5 →
      Lam0BoundOther χ₁ ρ₁ (min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / lamOf q ρ₁))) := by
  classical
  obtain ⟨δ, hδ0, hδ1, q52, h52⟩ := t23l52
  obtain ⟨qS, hS⟩ := t23simple
  obtain ⟨qW, hW⟩ := t23GlueWitness_of_logFreeCount hcount δ hδ0 hδ1
  obtain ⟨qG, hG⟩ := t23glue δ hδ0 hδ1
  obtain ⟨qA, hA⟩ := exists_log_ge (4 * Real.exp 1 / δ)
  obtain ⟨qB, hB⟩ := exists_lamMax_ge (4 * Real.exp 1)
  refine ⟨({qA, qB, q52, qS, qW, qG, 3} : Finset ℕ).max' (by simp), ?_⟩
  intro q hq inst χ₁ ρ₁ hwide hsq him0 hlamS h15
  have hqA : qA ≤ q := le_trans (Finset.le_max' _ qA (by simp)) hq
  have hqB : qB ≤ q := le_trans (Finset.le_max' _ qB (by simp)) hq
  have hq52 : q52 ≤ q := le_trans (Finset.le_max' _ q52 (by simp)) hq
  have hqS : qS ≤ q := le_trans (Finset.le_max' _ qS (by simp)) hq
  have hqW : qW ≤ q := le_trans (Finset.le_max' _ qW (by simp)) hq
  have hqG : qG ≤ q := le_trans (Finset.le_max' _ qG (by simp)) hq
  have hq3 : 3 ≤ q := le_trans (Finset.le_max' _ 3 (by simp)) hq
  have hq2 : 2 ≤ q := by omega
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ1 : χ₁ ≠ 1 := (isMin1_isZ hwide.1).1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := (isMin1_isZ hwide.1).2.1
  obtain ⟨hre1pos, hre1lt, hlam1pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
  have hρ₁eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have hsimple : zeroMult χ₁ ρ₁ = 1 := by
    have h : zeroMult χ₁ ((ρ₁.re : ℝ) : ℂ) = 1 :=
      hS q hqS χ₁ ρ₁.re hχ1 hsq hre1lt (by rw [← hρ₁eq]; exact hzm1)
        (fun u hzu himu => by
          rw [← hρ₁eq]
          exact hwide.2 χ₁ u hχ1 hzu (by linarith [abs_le.mp himu]))
        (by rw [← hρ₁eq]; linarith)
    rw [congrArg (fun z => zeroMult χ₁ z) hρ₁eq]
    exact h
  have hL52 : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε' δ :=
    fun ε' hε' hε'1 => h52 q hq52 χ₁ hχ1 hsq ε' hε' hε'1
  have hcap_thr : 4 * Real.exp 1 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := hB q hqB
  have hδ_thr : 4 * Real.exp 1 ≤ δ * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hδ0).mp (hA q hqA)
    linarith
  have hlog1nn : 0 ≤ Real.log (1 / lamOf q ρ₁) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hlam1pos]
    linarith
  intro ρ hZ hne hconj
  by_contra hlt
  push_neg at hlt
  have hmin_le : min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / lamOf q ρ₁))
      ≤ min (4 * Real.exp 1) (2 * Real.log (1 / lamOf q ρ₁)) := by
    refine le_min (min_le_left _ _) ?_
    exact le_trans (min_le_right _ _) (by nlinarith [hlog1nn, hε])
  have hlt4e : lamOf q ρ < 4 * Real.exp 1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hcapρ : lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
    le_trans hlt4e.le hcap_thr
  have hδρ : lamOf q ρ ≤ δ * Real.log (q : ℝ) := le_trans hlt4e.le hδ_thr
  obtain ⟨ρ', Hb, hzm', hne', him', hHb', hleu, hmax⟩ :=
    hW q hqW χ₁ ρ₁ ρ hwide hsq him0 hZ hne hcapρ hδρ
  have hcap' : lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := le_trans hleu hcapρ
  have hδρ' : lamOf q ρ' ≤ δ * Real.log (q : ℝ) := le_trans hleu hδρ
  obtain ⟨p, hp, hbp, hvp⟩ := t23cover.1 (lamOf q ρ₁) hlam1pos h15
  have hpm : p ∈ t23rows ++ rowG := List.mem_append.mpr (Or.inl hp)
  have hlammem : p.1 ∈ t23lams := t23lamsmem p hpm
  have hp1pos : 0 < p.1 := t23pos p hpm
  have hineq := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him' hHb' hmax hcap' hδρ'
    (by linarith : lamOf q ρ₁ ≤ 2 / 5) hsimple hL52 p.1 hlammem hp1pos
  have hcert := RowCert_all p hp
  have hvle : p.2.2 ≤ lamOf q ρ' :=
    row_bound₀ hp1pos hineq hcert hbp hlam1pos.le
  linarith [hmin_le, hvp, hleu, hlt, hvle]

/-! ## The second conjunct of `HBTable2and3` -/

/-- **HB Table 3** (the second conjunct of `HBTable2and3`): for `λ₁ ≤ 2/5` every other zero of `χ₁`
in the working region has `λ ≥ max ((3/2) log (1/λ₁)) (1294/1000)`. -/
theorem hb23_conj2 (hcount : NearLineCountLogFree) (lamS : ℝ) (hlamS : 0 < lamS) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS ≤ lamOf q ρ₁ →
      lamOf q ρ₁ ≤ 2 / 5 →
      Lam0BoundOther χ₁ ρ₁ (max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000)) := by
  classical
  obtain ⟨δ, hδ0, hδ1, q52, h52⟩ := t23l52
  obtain ⟨qS, hS⟩ := t23simple
  obtain ⟨qW, hW⟩ := t23GlueWitness_of_logFreeCount hcount δ hδ0 hδ1
  obtain ⟨qG, hG⟩ := t23glue δ hδ0 hδ1
  set Λ : ℝ := max ((3 / 2) * Real.log (1 / lamS)) (1294 / 1000) with hΛ
  obtain ⟨qA, hA⟩ := exists_log_ge (Λ / δ)
  obtain ⟨qB, hB⟩ := exists_lamMax_ge Λ
  refine ⟨({qA, qB, q52, qS, qW, qG, 3} : Finset ℕ).max' (by simp), ?_⟩
  intro q hq inst χ₁ ρ₁ hwide hsq him0 hlamS' h25
  have hqA : qA ≤ q := le_trans (Finset.le_max' _ qA (by simp)) hq
  have hqB : qB ≤ q := le_trans (Finset.le_max' _ qB (by simp)) hq
  have hq52 : q52 ≤ q := le_trans (Finset.le_max' _ q52 (by simp)) hq
  have hqS : qS ≤ q := le_trans (Finset.le_max' _ qS (by simp)) hq
  have hqW : qW ≤ q := le_trans (Finset.le_max' _ qW (by simp)) hq
  have hqG : qG ≤ q := le_trans (Finset.le_max' _ qG (by simp)) hq
  have hq3 : 3 ≤ q := le_trans (Finset.le_max' _ 3 (by simp)) hq
  have hq2 : 2 ≤ q := by omega
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ1 : χ₁ ≠ 1 := (isMin1_isZ hwide.1).1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := (isMin1_isZ hwide.1).2.1
  obtain ⟨hre1pos, hre1lt, hlam1pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
  have hρ₁eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have hsimple : zeroMult χ₁ ρ₁ = 1 := by
    have h : zeroMult χ₁ ((ρ₁.re : ℝ) : ℂ) = 1 :=
      hS q hqS χ₁ ρ₁.re hχ1 hsq hre1lt (by rw [← hρ₁eq]; exact hzm1)
        (fun u hzu himu => by
          rw [← hρ₁eq]
          exact hwide.2 χ₁ u hχ1 hzu (by linarith [abs_le.mp himu]))
        (by rw [← hρ₁eq]; linarith)
    rw [congrArg (fun z => zeroMult χ₁ z) hρ₁eq]
    exact h
  have hL52 : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + 1 / 1000000) ε' δ :=
    fun ε' hε' hε'1 => h52 q hq52 χ₁ hχ1 hsq ε' hε' hε'1
  have hΛcap : Λ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := hB q hqB
  have hΛδ : Λ ≤ δ * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hδ0).mp (hA q hqA)
    linarith
  have hv₂Λ : max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000) ≤ Λ := by
    refine max_le ?_ (le_max_right _ _)
    have hdiv : 1 / lamOf q ρ₁ ≤ 1 / lamS := one_div_le_one_div_of_le hlamS hlamS'
    have hlog := Real.log_le_log (by positivity) hdiv
    have := le_max_left ((3 / 2) * Real.log (1 / lamS)) (1294 / 1000 : ℝ)
    linarith
  intro ρ hZ hne hconj
  by_cases hcase : (1 / 1000 : ℝ) ≤ lamOf q ρ₁
  · -- the rows of Tables 2/3 cover the whole range `[10⁻³, 2/5]`
    by_contra hlt
    push_neg at hlt
    have hltΛ : lamOf q ρ < Λ := lt_of_lt_of_le hlt hv₂Λ
    have hcapρ : lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
      le_trans hltΛ.le hΛcap
    have hδρ : lamOf q ρ ≤ δ * Real.log (q : ℝ) := le_trans hltΛ.le hΛδ
    obtain ⟨ρ', Hb, hzm', hne', him', hHb', hleu, hmax⟩ :=
      hW q hqW χ₁ ρ₁ ρ hwide hsq him0 hZ hne hcapρ hδρ
    have hcap' : lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := le_trans hleu hcapρ
    have hδρ' : lamOf q ρ' ≤ δ * Real.log (q : ℝ) := le_trans hleu hδρ
    rcases t23cover.2 (lamOf q ρ₁) hcase h25 with ⟨p, hp, hbp, hvp⟩ | ⟨p, hp, hbp, hvp⟩
    · have hpm : p ∈ t23rows ++ rowG := List.mem_append.mpr (Or.inl hp)
      have hlammem : p.1 ∈ t23lams := t23lamsmem p hpm
      have hp1pos : 0 < p.1 := t23pos p hpm
      have hineq := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him' hHb' hmax hcap' hδρ'
        h25 hsimple hL52 p.1 hlammem hp1pos
      have hcert := RowCert_all p hp
      have hvle : p.2.2 ≤ lamOf q ρ' := row_bound₀ hp1pos hineq hcert hbp hlam1pos.le
      linarith [hvp, hleu, hlt, hvle]
    · have hpm : p ∈ t23rows ++ rowG := List.mem_append.mpr (Or.inr hp)
      have hlammem : p.1 ∈ t23lams := t23lamsmem p hpm
      have hp1pos : 0 < p.1 := t23pos p hpm
      have hineq := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him' hHb' hmax hcap' hδρ'
        h25 hsimple hL52 p.1 hlammem hp1pos
      have hcert := t23certG p hp
      have hvle : p.2.2 ≤ lamOf q ρ' := row_bound₀ hp1pos hineq hcert hbp hlam1pos.le
      linarith [hvp, hleu, hlt, hvle]
  · -- `λ₁ < 10⁻³`: the fixed scale `λ = 3` argument
    push_neg at hcase
    by_contra hlt
    push_neg at hlt
    have h1294 : (1294 / 1000 : ℝ) ≤ (3 / 2) * Real.log (1 / lamOf q ρ₁) :=
      one_two_nine_four_le hlam1pos hcase.le
    have hv₂ : max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000)
        = (3 / 2) * Real.log (1 / lamOf q ρ₁) := max_eq_left h1294
    rw [hv₂] at hlt
    have hltΛ : lamOf q ρ < Λ := by
      have hlog : Real.log (1 / lamOf q ρ₁) ≤ Real.log (1 / lamS) := by
        have hdiv : 1 / lamOf q ρ₁ ≤ 1 / lamS := one_div_le_one_div_of_le hlamS hlamS'
        exact Real.log_le_log (by positivity) hdiv
      have hmaxl := le_max_left ((3 / 2) * Real.log (1 / lamS)) (1294 / 1000 : ℝ)
      linarith
    have hcapρ : lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 :=
      le_trans hltΛ.le hΛcap
    have hδρ : lamOf q ρ ≤ δ * Real.log (q : ℝ) := le_trans hltΛ.le hΛδ
    obtain ⟨ρ', Hb, hzm', hne', him', hHb', hleu, hmax⟩ :=
      hW q hqW χ₁ ρ₁ ρ hwide hsq him0 hZ hne hcapρ hδρ
    have hcap' : lamOf q ρ' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := le_trans hleu hcapρ
    have hδρ' : lamOf q ρ' ≤ δ * Real.log (q : ℝ) := le_trans hleu hδρ
    have h15 : lamOf q ρ₁ ≤ 1 / 5 := by linarith
    -- a row of Table 2 gives `λ(ρ') ≥ min (4e) (2 log (1/λ₁)) ≥ 4`
    obtain ⟨p, hp, hbp, hvp⟩ := t23cover.1 (lamOf q ρ₁) hlam1pos h15
    have hpm : p ∈ t23rows ++ rowG := List.mem_append.mpr (Or.inl hp)
    have hlammem : p.1 ∈ t23lams := t23lamsmem p hpm
    have hp1pos : 0 < p.1 := t23pos p hpm
    have hineq := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him' hHb' hmax hcap' hδρ'
      (by linarith : lamOf q ρ₁ ≤ 2 / 5) hsimple hL52 p.1 hlammem hp1pos
    have hcert := RowCert_all p hp
    have hfour : (4 : ℝ) ≤ lamOf q ρ' :=
      le_trans (le_trans (four_le_min hlam1pos hcase.le) hvp)
        (row_bound₀ hp1pos hineq hcert hbp hlam1pos.le)
    -- the §6 inequality at the fixed scale `3`
    have hineq3 := hG q hqG χ₁ ρ₁ ρ' Hb hwide hsq him0 hzm' hne' him' hHb' hmax hcap' hδρ'
      (by linarith : lamOf q ρ₁ ≤ 2 / 5) hsimple hL52 3 (by simp [t23lams]) (by norm_num)
    have h3 : 8 / 9 - CertSlack * (16 * 3 / 15)
        ≤ (1 / 15) * (hb72G (lamOf q ρ' / 3) - hb72G ((lamOf q ρ' - lamOf q ρ₁) / 3)) :=
      hb63_G (by norm_num) hineq3
    have hge : Real.exp (-(2 / 3) * lamOf q ρ') ≤ lamOf q ρ₁ := by
      by_contra hc
      push_neg at hc
      exact absurd (t23lam3 hfour hlam1pos hc t23lam3num) (not_lt.mpr h3)
    have hlog_le : Real.log (1 / lamOf q ρ₁) ≤ (2 / 3) * lamOf q ρ' := by
      have h := Real.log_le_log (Real.exp_pos (-(2 / 3) * lamOf q ρ')) hge
      rw [Real.log_exp] at h
      rw [one_div, Real.log_inv]
      linarith
    linarith [hleu, hlog_le, hlt]

/-! ## The engine -/

/-- **HB Tables 2 and 3** from the log-free near-line count. -/
theorem HBTable2and3_of_count (hcount : NearLineCountLogFree) :
    Work.ZeroFreeTables.HBTable2and3 := by
  intro ε hε lamS hlamS
  obtain ⟨q1, h1⟩ := hb23_conj1 hcount ε hε lamS hlamS
  obtain ⟨q2, h2⟩ := hb23_conj2 hcount lamS hlamS
  refine ⟨max q1 q2, ?_⟩
  intro q hq inst χ₁ ρ₁ hwide hsq him0 hlamS'
  have hq1 : q1 ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : q2 ≤ q := le_trans (le_max_right _ _) hq
  exact ⟨h1 q hq1 χ₁ ρ₁ hwide hsq him0 hlamS',
    fun h15 => h2 q hq2 χ₁ ρ₁ hwide hsq him0 hlamS' h15⟩

theorem HBTable2and3_all : Work.ZeroFreeTables.HBTable2and3 :=
  HBTable2and3_of_count t23NearLineCountLogFree_holds

end

end Work.ZeroFreeTables
