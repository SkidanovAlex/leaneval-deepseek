/-
# ZeroFreeTables/t23witness — `GlueWitness` from a log-free near-line zero count

`Work.ZeroFreeTables.GlueWitness` asks, for every window radius `δ ∈ (0,1/2]` and all large `q`:
given a real character `χ₁` mod `q` with a real λ-minimal zero `ρ₁` (`IsMin1WideAt 10`) and a
near-line zero `ρ ≠ ρ₁` (`λ(ρ) ≤ (1/3)logloglog q`, `|Im ρ| ≤ 1`, `λ(ρ) ≤ δ log q`), there are a
zero `ρ' ≠ ρ₁` of `χ₁` and a box height `Hb ≥ |Im ρ'| + δ` with `|Im ρ'| ≤ 10 log q`,
`λ(ρ') ≤ λ(ρ)` and `ρ'` `λ`-minimal among the zeros of `χ₁` other than `ρ₁` in the box
`|Im| ≤ Hb`.

**The content of the existence of such a `ρ'` is a near-line zero count.**  If the number of
zeros `u` of `χ₁` with `λ(u) ≤ t ≤ (1/3)·logloglog q` and `|Im u| ≤ 10 log q` is at most
`C log q` with `C < 10`, the pigeonhole over the levels `1 + j/2` yields a level-`j`
`λ`-minimiser whose window `|Im| ≤ |Im ρ'| + 1/2` fits in its own box: this is
`Work.LinnikAreas.DhRepel.witnessOfCount`, whose proof is reproduced below in the exact
hypotheses of `GlueWitness` (`IsMin1WideAt 10`, `ρ₁.im = 0`, arbitrary `δ ≤ 1/2`, plus the point
condition `λ(ρ) ≤ δ log q`).

That count is *not* available in the current workspace: it is the log-free near-line zero count
(a consequence of Jutila's log-free zero-density estimate = Heath-Brown's Principle 3, recorded
here as the `sorry`-ed node `Work.ZeroDensity.Jutila.jutilaNonPrincipal`, whose proof is reduced
to the missing `J`-bound of Jutila §3).  Accordingly this file contains

* `t23GlueWitness_of_logFreeCount` : a log-free count `≤ C (log q)^A`, `A < 1` ⟹ `GlueWitness`
  (complete, sorry-free), via the proved `Work.LinnikAreas.DhRepel.countOfLogFree`;
* `t23_witness_small_lambda` : the case `λ(ρ) < min(c, 1/100)` of the off-axis zero-free
  constant `c` (`Work.LinnikAreas.offAxisConstWide`), proved unconditionally from the zero-free
  region and the real-zero count `Work.LinnikAreas.realZeroLambdaCountLinear`;
* `t23witness` : the requested statement, reduced to those two pieces.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.LinnikAreas.boxMaxZeroH
import Submission.Work.LinnikAreas.DhRepel.countOfLogFree
import Submission.Work.LinnikAreas.exists_minLam_zero
import Submission.Work.ZeroFreeTables.t23NearLineCount
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikAreas.DhRepel.farZeroLambdaLower

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The off-axis zero-free region for non-real zeros (all heights `≤ 10 log q`)

`Work.LinnikAreas.offAxisConstWide` gives `λ(u) ≥ c` for zeros with `1 ≤ |Im u| ≤ 10 log q`;
its proof only uses `Im u ≠ 0`, so the same constant works for every *non-real* zero in the
strip. -/
private theorem t23_offAxis_nonreal :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ u : ℂ, zeroMult χ u ≠ 0 →
      u.im ≠ 0 → |u.im| ≤ 10 * Real.log (q : ℝ) → c ≤ lamOf q u := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  refine ⟨c₁ / 3, by positivity, 10, ?_⟩
  intro q hq hqne χ hχ u hz himne himu
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hqposN : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq10 : (10 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hLz : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    Work.LinnikAreas.DhRepel.LFunction_primitive_eq_zero χ hχ hz
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hψne : χ.primitiveCharacter ≠ 1 := Work.LinnikAreas.DhRepel.primitive_ne_one' hχ
  have hN1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor)
  have hNq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqposN χ.conductor_dvd_level
  have harg : (χ.conductor : ℝ) * (|u.im| + 2) ≤ (q : ℝ) ^ 3 := by
    have h1 : |u.im| + 2 ≤ 10 * Real.log (q : ℝ) + 2 := by linarith [himu]
    have h2 : 10 * Real.log (q : ℝ) + 2 ≤ (q : ℝ) ^ 2 := by
      have h3 : Real.log (q : ℝ) ≤ (q : ℝ) - 1 := Real.log_le_sub_one_of_pos hqpos
      have h4 : (0 : ℝ) ≤ ((q : ℝ) - 10) * (q : ℝ) := mul_nonneg (by linarith) hqpos.le
      nlinarith [h3, h4]
    have h5 : (0 : ℝ) < |u.im| + 2 := by positivity
    calc (χ.conductor : ℝ) * (|u.im| + 2) ≤ (q : ℝ) * ((q : ℝ) ^ 2) :=
          mul_le_mul hNq (le_trans h1 h2) h5.le hqpos.le
      _ = (q : ℝ) ^ 3 := by ring
  have hlogt : Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ 3 * Real.log (q : ℝ) := by
    calc Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) ≤ Real.log ((q : ℝ) ^ 3) :=
          Real.log_le_log (by positivity) harg
      _ = 3 * Real.log (q : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hargpos : 0 < Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
    apply Real.log_pos
    nlinarith [hN1, abs_nonneg u.im]
  have hkey : c₁ / (3 * Real.log (q : ℝ)) < 1 - u.re := by
    have hL0' : DirichletCharacter.LFunction χ.primitiveCharacter
        ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = 0 := by
      rw [Complex.re_add_im u]; exact hLz
    have hlt : u.re < 1 - c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
      by_contra hcon
      push Not at hcon
      exact (hc₁ χ.primitiveCharacter hψprim hψne u.re u.im himne hcon) hL0'
    have hmono : c₁ / (3 * Real.log (q : ℝ))
        ≤ c₁ / Real.log ((χ.conductor : ℝ) * (|u.im| + 2)) := by
      rw [div_le_div_iff₀ (by positivity) hargpos]
      nlinarith [hlogt, hc₁pos]
    linarith
  rw [lamOf]
  have hmul : c₁ / (3 * Real.log (q : ℝ)) * Real.log (q : ℝ) = c₁ / 3 := by
    field_simp
  rw [← hmul]
  exact le_of_lt (mul_lt_mul_of_pos_right hkey hlogpos)

/-! ## The assembly: a near-line zero count gives the witness -/

/-- The support of the multiplicity-weighted zero count of `χ` in the box `|Im u| ≤ R`,
`λ(u) ≤ t` is finite (for `2 ≤ q`, so that `log q > 0`): it is contained in the box
`1 - t/log q ≤ Re ≤ 1`, `|Im| ≤ R`. -/
private theorem t23_support_count_finite {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (t R : ℝ) :
    (Function.support (fun u : ℂ =>
      if zeroMult χ u ≠ 0 ∧ |u.im| ≤ R ∧ lamOf q u ≤ t
        then (zeroMult χ u : ℝ) else 0)).Finite := by
  classical
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - t / Real.log q) R).subset ?_
  intro u hu
  rw [Function.mem_support] at hu
  by_cases hc : zeroMult χ u ≠ 0 ∧ |u.im| ≤ R ∧ lamOf q u ≤ t
  · rw [if_pos hc] at hu
    obtain ⟨hzm, him, hlam⟩ := hc
    rw [lamOf] at hlam
    have h1 : 1 - u.re ≤ t / Real.log q := (le_div_iff₀ hlogpos).mpr hlam
    exact ⟨hzm, by linarith, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm),
      him⟩
  · rw [if_neg hc] at hu
    exact absurd rfl hu

/-- A bound on a finitely supported `∑ᶠ` all of whose values are at least `1` on the support
bounds the cardinality of the support. -/
private theorem t23_card_le_of_finsum_le {f : ℂ → ℝ} (hfin : (Function.support f).Finite)
    (hone : ∀ u, f u ≠ 0 → 1 ≤ f u) {B : ℝ} (hB : (∑ᶠ u : ℂ, f u) ≤ B) :
    ((hfin.toFinset.card : ℕ) : ℝ) ≤ B := by
  classical
  have hfs : (∑ᶠ u : ℂ, f u) = ∑ u ∈ hfin.toFinset, f u :=
    finsum_eq_sum_of_support_subset f (by rw [Set.Finite.coe_toFinset])
  have h1 : ((hfin.toFinset.card : ℕ) : ℝ) ≤ ∑ u ∈ hfin.toFinset, f u := by
    have h := Finset.card_nsmul_le_sum hfin.toFinset f (1 : ℝ)
      (fun u hu => hone u (Function.mem_support.mp ((Set.Finite.mem_toFinset hfin).mp hu)))
    simpa using h
  rw [hfs] at hB
  linarith

/-- **Pigeonhole in `card S + 1` horizontal levels.**  If the `card S + 1` points `v j` all lie
in `S` and satisfy `|Im (v j)| ≤ 1 + j/2`, then for some `j` the window
`|Im (v j)| + 1/2` of `v j` is contained in the level `1 + j/2`; otherwise the `v j` would be
`card S + 1` distinct elements of `S`. -/
private theorem t23_window_pigeonhole (S : Finset ℂ) (v : Fin (S.card + 1) → ℂ)
    (hv : ∀ j, v j ∈ S) (hb : ∀ j, |(v j).im| ≤ 1 + (j.val : ℝ) / 2) :
    ∃ j : Fin (S.card + 1), |(v j).im| + 1 / 2 ≤ 1 + (j.val : ℝ) / 2 := by
  classical
  by_contra h
  push_neg at h
  have key : ∀ j k : Fin (S.card + 1), j.val < k.val → v j ≠ v k := by
    intro j k hlt hEq
    have hk : 1 ≤ k.val := by omega
    have hcast : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; norm_num
    have hmono : (1 : ℝ) + (j.val : ℝ) / 2 ≤ 1 + ((k.val - 1 : ℕ) : ℝ) / 2 := by
      have hjle : j.val ≤ k.val - 1 := by omega
      have : (j.val : ℝ) ≤ ((k.val - 1 : ℕ) : ℝ) := by exact_mod_cast hjle
      linarith
    have hstrict : (1 : ℝ) + ((k.val - 1 : ℕ) : ℝ) / 2 < |(v k).im| := by
      have hh := h k
      rw [hcast]
      linarith
    have hup : |(v j).im| ≤ 1 + (j.val : ℝ) / 2 := hb j
    rw [hEq] at hup
    linarith
  have hinj : Function.Injective v := by
    intro j k hjk
    by_contra hne
    rcases lt_trichotomy j.val k.val with hlt | heq | hgt
    · exact key j k hlt hjk
    · exact hne (Fin.ext heq)
    · exact key k j hgt hjk.symm
  have hcard := Fintype.card_le_of_injective
    (fun j : Fin (S.card + 1) => (⟨v j, hv j⟩ : S))
    (fun j k h => hinj (Subtype.ext_iff.mp h))
  simp only [Fintype.card_coe, Fintype.card_fin] at hcard
  exact absurd hcard (by omega)

/-- **The witness from a `C log q` near-line count (`C < 10`).**  This is the pigeonhole of
`Work.LinnikAreas.DhRepel.witnessOfCount`, with the hypotheses of `GlueWitness` and with the
window margin `1/2`; the conclusion for a general `δ ≤ 1/2` follows by reusing the same pair
`(ρ', Hb)`. -/
theorem t23GlueWitness_of_count
    (hcount : ∃ C : ℝ, 0 < C ∧ C < 10 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
      t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
          |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
        then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
        ≤ C * Real.log (q : ℝ)) :
    Work.ZeroFreeTables.GlueWitness := by
  classical
  intro δ hδ0 hδ1
  obtain ⟨C, hCpos, hClt, qc, hcount⟩ := hcount
  refine ⟨max 3 qc, ?_⟩
  intro q hq inst χ₁ ρ₁ ρ hmin1 hsq hrho0im hZ hne hlamT hlamδ
  have hchi : χ₁ ≠ 1 := hZ.1
  have hq3 : 3 ≤ q := le_trans (le_max_left 3 qc) hq
  have hqqc : qc ≤ q := le_trans (le_max_right 3 qc) hq
  have hq2 : 2 ≤ q := by omega
  have hzmrho : Work.LinnikContract.zeroMult χ₁ ρ ≠ 0 := hZ.2.1
  have him1 : |ρ.im| ≤ 1 := hZ.2.2
  let L : ℝ := Real.log (q : ℝ)
  let T : ℝ := Real.log (Real.log (Real.log (q : ℝ))) / 3
  have hL1 : 1 ≤ L := by
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have he3 : Real.exp 1 ≤ (q : ℝ) := le_trans (le_of_lt Real.exp_one_lt_three) h3
    have h := Real.log_le_log (Real.exp_pos 1) he3
    rw [Real.log_exp] at h
    simpa [L] using h
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlampos : 0 < Work.LinnikContract.lamOf q ρ := by
    rw [Work.LinnikContract.lamOf]
    have h1 : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzmrho
    nlinarith
  have hTpos : 0 < T := lt_of_lt_of_le hlampos hlamT
  have hsum : (∑ᶠ u : ℂ, (if Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
      Work.LinnikContract.lamOf q u ≤ T then (Work.LinnikContract.zeroMult χ₁ u : ℝ) else 0))
      ≤ C * L := hcount q hqqc χ₁ hchi T hTpos.le le_rfl
  have hsupp : (Function.support (fun u : ℂ =>
      if Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
        Work.LinnikContract.lamOf q u ≤ T
        then (Work.LinnikContract.zeroMult χ₁ u : ℝ) else 0)).Finite :=
    t23_support_count_finite (q := q) hq2 χ₁ T (10 * L)
  set S : Finset ℂ := hsupp.toFinset with hSdef
  have hSmem : ∀ u : ℂ, u ∈ S ↔ (Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
      Work.LinnikContract.lamOf q u ≤ T) := by
    intro u
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support]
    by_cases hc : (Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
        Work.LinnikContract.lamOf q u ≤ T)
    · rw [if_pos hc]; simp [hc]
    · rw [if_neg hc]; simp [hc]
  have hcard : ((S.card : ℕ) : ℝ) ≤ C * L := by
    have h := t23_card_le_of_finsum_le (f := fun u : ℂ =>
        if Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
          Work.LinnikContract.lamOf q u ≤ T
          then (Work.LinnikContract.zeroMult χ₁ u : ℝ) else 0)
      hsupp (fun u hu => by
        by_cases hc : (Work.LinnikContract.zeroMult χ₁ u ≠ 0 ∧ |u.im| ≤ 10 * L ∧
            Work.LinnikContract.lamOf q u ≤ T)
        · rw [if_pos hc]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc.1
        · rw [if_neg hc] at hu
          exact absurd rfl hu) hsum
    rwa [← hSdef] at h
  have hn10 : ((S.card : ℕ) : ℝ) < 10 * L := by
    have h10 : C * L < 10 * L := mul_lt_mul_of_pos_right hClt hLpos
    linarith
  have hH10 : ∀ j : ℕ, j ≤ S.card → (1 : ℝ) + (j : ℝ) / 2 ≤ 10 * L := by
    intro j hj
    have hj' : (j : ℝ) ≤ ((S.card : ℕ) : ℝ) := by exact_mod_cast hj
    have h5 : 5 * L ≤ 10 * L - 1 := by linarith
    linarith
  have hex : ∀ j : Fin (S.card + 1), ∃ v : ℂ, Work.LinnikContract.zeroMult χ₁ v ≠ 0 ∧
      |v.im| ≤ 1 + (j.val : ℝ) / 2 ∧ v ≠ ρ₁ ∧
      Work.LinnikContract.lamOf q v ≤ Work.LinnikContract.lamOf q ρ ∧
      ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 + (j.val : ℝ) / 2 →
        u ≠ ρ₁ → Work.LinnikContract.lamOf q v ≤ Work.LinnikContract.lamOf q u := by
    intro j
    refine Work.LinnikAreas.boxMaxZeroH hq2 χ₁ ρ₁ ρ ?_ hzmrho him1 hne
    have hnn : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg j.val
    linarith
  choose v hv using hex
  have hvS : ∀ j : Fin (S.card + 1), v j ∈ S := by
    intro j
    rw [hSmem]
    exact ⟨(hv j).1, le_trans (hv j).2.1 (hH10 j.val (by omega)),
      le_trans (hv j).2.2.2.1 hlamT⟩
  by_cases hwit : ∃ j : Fin (S.card + 1), |(v j).im| + 1 / 2 ≤ 1 + (j.val : ℝ) / 2
  · obtain ⟨j, hj⟩ := hwit
    refine ⟨v j, 1 + (j.val : ℝ) / 2, (hv j).1, (hv j).2.2.1, ?_, ?_, (hv j).2.2.2.1, ?_⟩
    · exact le_trans (hv j).2.1 (hH10 j.val (by omega))
    · linarith
    · intro u hzu himu
      rcases eq_or_ne u ρ₁ with rfl | hne'
      · exact Or.inl rfl
      · exact Or.inr ((hv j).2.2.2.2 u hzu himu hne')
  · exfalso
    exact hwit (t23_window_pigeonhole S v hvS (fun j => (hv j).2.1))

/-- **The witness from a log-free near-line count** `≤ C (log q)^A` with `A < 1`, converted to
the `C < 10` form by `Work.LinnikAreas.DhRepel.countOfLogFree`. -/
theorem t23GlueWitness_of_logFreeCount
    (hcount : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ A < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
        t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
          ≤ C * (Real.log (q : ℝ)) ^ A) :
    Work.ZeroFreeTables.GlueWitness :=
  t23GlueWitness_of_count (Work.LinnikAreas.DhRepel.countOfLogFree hcount)

/-! ## Case A: the given zero is below the off-axis zero-free constant -/

/-- **The witness when `λ(ρ)` is below the off-axis zero-free constant `c`.**  Then the
`λ`-minimiser `u` over the working region `|Im| ≤ 1` (which exists,
`Work.LinnikAreas.exists_minLam_zero`) has `λ(u) ≤ λ(ρ) < c`, hence is real; every other zero of
`χ₁` in the box `|Im| ≤ δ` is either real (and dominated by the minimality of `u`) or non-real,
hence has `λ ≥ c > λ(ρ) ≥ λ(u)`.  Thus `(u, δ)` is a witness. -/
private theorem t23_witness_small_lambda (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
      χ₁ ≠ 1 → zeroMult χ₁ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₁ →
      lamOf q ρ < c →
      ∃ (ρ' : ℂ) (Hb : ℝ), zeroMult χ₁ ρ' ≠ 0 ∧ ρ' ≠ ρ₁ ∧
        |ρ'.im| ≤ 10 * Real.log (q : ℝ) ∧ |ρ'.im| + δ ≤ Hb ∧
        lamOf q ρ' ≤ lamOf q ρ ∧
        (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
          u = ρ₁ ∨ lamOf q ρ' ≤ lamOf q u) := by
  obtain ⟨cZ, hcZpos, qZ, hZ⟩ := t23_offAxis_nonreal
  refine ⟨cZ, hcZpos, max qZ 3, ?_⟩
  intro q hq inst χ₁ ρ₁ ρ hχ hz him hne hsmall
  have hqZ : qZ ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  -- `1 ≤ log q` (so that `10 log q` covers the box `|Im| ≤ δ ⊆ |Im| ≤ 1/2`)
  have hL1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have he3 : Real.exp 1 ≤ (q : ℝ) := le_trans (le_of_lt Real.exp_one_lt_three) h3
    have h := Real.log_le_log (Real.exp_pos 1) he3
    rwa [Real.log_exp] at h
  -- the `λ`-minimiser over the working region `|Im| ≤ 1`
  obtain ⟨u, huz, hue, huim, hule, hmin⟩ :=
    Work.LinnikAreas.exists_minLam_zero χ₁ hχ ρ₁ ρ 1 hz him hne
  -- it is real: `λ(u) ≤ λ(ρ) < cZ` and every non-real zero has `λ ≥ cZ`
  have huim0 : u.im = 0 := by
    by_contra h
    have hint : |u.im| ≤ 10 * Real.log (q : ℝ) := by
      have h10 : (1 : ℝ) / 2 ≤ 10 * Real.log (q : ℝ) := by linarith
      linarith
    have hbound := hZ q hqZ χ₁ hχ u huz h hint
    linarith
  have huim_ge : (0 : ℝ) ≤ 10 * Real.log (q : ℝ) := by
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have h4 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
      have he3 : Real.exp 1 ≤ (q : ℝ) := le_trans (le_of_lt Real.exp_one_lt_three) h3
      have h := Real.log_le_log (Real.exp_pos 1) he3
      rwa [Real.log_exp] at h
    linarith
  refine ⟨u, δ, huz, hue, ?_, ?_, hule, ?_⟩
  · rw [huim0]; simpa using huim_ge
  · rw [huim0]; simp
  · intro z hzz hzim
    rcases eq_or_ne z ρ₁ with rfl | hzne
    · exact Or.inl rfl
    · refine Or.inr ?_
      by_cases hzreal : z.im = 0
      · by_cases hzle : lamOf q z ≤ lamOf q ρ
        · refine hmin z hzz hzne ?_ hzle
          rw [hzreal]; simp
        · push_neg at hzle
          linarith
      · have hint : |z.im| ≤ 10 * Real.log (q : ℝ) := by
          have h1 : |z.im| ≤ 1 / 2 := by
            rw [abs_le] at hzim ⊢
            constructor <;> linarith [hzim.1, hzim.2, hδ0]
          have h2 : (1 : ℝ) / 2 ≤ 10 * Real.log (q : ℝ) := by linarith
          linarith
        have hbound := hZ q hqZ χ₁ hχ z hzz hzreal hint
        linarith

/-- **`GlueWitness` in the case `λ(ρ) < c`**: the unconditional half of the requested statement,
with `c` the off-axis zero-free constant of `t23_witness_small_lambda`. -/
theorem t23GlueWitness_small_lambda :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → IsZ χ₁ ρ → ρ ≠ ρ₁ →
        lamOf q ρ ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        lamOf q ρ ≤ δ * Real.log (q : ℝ) → lamOf q ρ < c →
        ∃ (ρ' : ℂ) (Hb : ℝ), zeroMult χ₁ ρ' ≠ 0 ∧ ρ' ≠ ρ₁ ∧
          |ρ'.im| ≤ 10 * Real.log (q : ℝ) ∧ |ρ'.im| + δ ≤ Hb ∧
          lamOf q ρ' ≤ lamOf q ρ ∧
          (∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
            u = ρ₁ ∨ lamOf q ρ' ≤ lamOf q u) := by
  intro δ hδ0 hδ1
  obtain ⟨c, hcpos, q₀, hq₀⟩ := t23_witness_small_lambda δ hδ0 hδ1
  exact ⟨c, hcpos, q₀, fun q hq inst χ₁ ρ₁ ρ hmin hsq hρ₁ hI hne hT hδ hsmall =>
    hq₀ q hq χ₁ ρ₁ ρ hI.1 hI.2.1 hI.2.2 hne hsmall⟩


/-! ## The requested statement -/

/-- **`Work.ZeroFreeTables.GlueWitness`**, from the log-free near-line zero count
`Work.ZeroFreeTables.t23NearLineCount` of a single character (the remaining deep input: Jutila's
log-free zero-density estimate, recorded as the node `Work.ZeroDensity.Jutila.jutilaNonPrincipal`)
via the pigeonhole assembly `t23GlueWitness_of_logFreeCount`. -/
theorem t23witness : Work.ZeroFreeTables.GlueWitness :=
  t23GlueWitness_of_logFreeCount Work.ZeroFreeTables.t23NearLineCount

end Work.ZeroFreeTables
