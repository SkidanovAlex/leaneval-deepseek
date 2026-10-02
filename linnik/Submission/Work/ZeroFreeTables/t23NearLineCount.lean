import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroDensity.Jutila.jutilaNonPrincipal
import Submission.Work.LinnikAreas.DhRepel.nearSumLeZeroCountIn
import Submission.Work.LinnikAreas.DhRepel.rpowArithLogFree
import Submission.Work.LinnikAreas.DhRepel.logLogLogDivThreeLeLogDivFive
import Submission.Work.LinnikAreas.FarBoundOfDensity
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

namespace Work.ZeroFreeTables

/-- A log-free near-line zero count for a single character (the input of `Work.ZeroFreeTables.GlueWitness`).

**STATUS OF THIS REQUEST (verdict: mis-scoped; the statement is TRUE but is the paper's imported
deep input in closed form).**  The proof below is *complete* and shows that the requested statement
follows from the recorded assumption node
`Work.ZeroDensity.Jutila.jutilaNonPrincipal` (Jutila, *On Linnik's constant*, Math. Scand. **41**
(1977) 45--62, Theorem 1, (1.7) = Heath-Brown (1992) Principle 3 / (1.4)) with `ε = 1/2`,
`T = 10 log q`, `σ = 1 - t/log q`, plus the proved glue `DhRepel.nearSumLeZeroCountIn`,
`Finset.single_le_sum` over `Finset.univ.erase 1`, and the proved arithmetic
`DhRepel.rpowArithLogFree`/`logLogLogDivThreeLeLogDivFive` (with `C = 1`, `A = 1/2`).  Hence the
only remaining input is the node itself; the axiom list of this theorem therefore contains the
placeholder axiom of that unproved node, so the lemma is *not* a closed axiom-free theorem of this
development.

The node is the project's recorded imported input: its formalisation needs Jutila §2--3, whose
crux (Lemma 6, the zero detector) is *not* stated anywhere in the workspace and cannot be
transcribed from the available sources (the Math. Scand. scan is image-only; see
`ZeroDensity/Jutila/NOTE_roadSection3.md` and the OCR note there), together with the §3 Halász
assembly (`not started`) and, for the far range `4/5 ≤ σ ≤ 5/6`, Huxley--Jutila IV (absent).  The
same disposition is recorded in this workspace for the sibling requests `t23JBound`,
`ownCountNearLineLogFree`, `jutilaLogFree` and `famCountJutilaNearLine`; the correct form of the
request is the conditional one, which is what this file proves (cf. the proved
`Work.LinnikAreas.DhRepel.nearLineCountLogFreeFromNode`,
`Work.LinnikAreas.nearLineCount_of_familyDensityJutila` and
`Work.LinnikAreas.DhRepel.nearLineCountFromNode`).


Route: `Work.ZeroDensity.Jutila.jutilaNonPrincipal` (non-principal log-free family count
`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C_ε (qT)^{(2+ε)(1-σ)}` on `4/5 ≤ σ ≤ 1`, `T ≥ 1`) applied at `ε := 1/2`,
`T := 10 log q`, `σ := 1 - t/(log q)`: the single character is dominated by the sum over
`Finset.univ.erase 1` as in the proved `Work.LinnikAreas.JMAuxSh.nearLineCount_of_jutilaNP`, and
`Work.LinnikAreas.zeroCountIn χ σ T` is exactly the multiplicity-weighted count over
`σ ≤ Re ≤ 1`, `|Im| ≤ T` (with `λ(u) ≤ t` forcing `Re u ≥ σ`).  The result is
`C_ε (q·10log q)^{(2+ε)t/log q} = C_ε e^{(2+ε)t}(1+o(1)) ≤ C_ε (log q)^{(2+ε)/3}` since
`(2+ε)t ≤ log log q`; `(2+ε)/3 = 5/6 < 1`, so this is the stated shape with `A := 5/6`.
The node `jutilaNonPrincipal` is currently an unproved node; its proof is reduced in that file (via the
proved `jutilaNonPrincipal_of_boxBound_and_jBound`) to the per-box count
`Work.ZeroDensity.Jutila.linnikDensityLemma` (proved) and the `J`-bound of Jutila §3, whose halves
are the detector (Jutila's pseudocharacter) and the bilinear form (Jutila's Lemma 2--4,
`Work.ZeroDensity.Jutila.lemma4BarbanVehovGraham`), glued by the proved
`Work.ZeroDensity.Jutila.halaszDualityFrame` and `Work.ZeroDensity.Jutila.wellSpacedExtraction`. -/
theorem t23NearLineCount :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ A < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
        t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
          ≤ C * (Real.log (q : ℝ)) ^ A := by
  -- Jutila's log-free non-principal family bound, in the chapter's form, at `ε = 1/2`
  obtain ⟨CJ, hCJ, hJ⟩ :=
    Work.LinnikAreas.familyZeroDensityJutilaNP_of_chapter
      Work.ZeroDensity.Jutila.jutilaNonPrincipal (1 / 2) (by norm_num)
  -- the arithmetic threshold: `CJ * (q * 10 log q)^(3 t/log q) ≤ (log q)^(1/2)`
  obtain ⟨qA, hqA⟩ := Work.LinnikAreas.DhRepel.rpowArithLogFree CJ (1 / 2) hCJ (by norm_num)
  -- the threshold at which `σ = 1 - t/log q ≥ 4/5`, and `log q ≥ 40`
  obtain ⟨X, hX⟩ := Work.LinnikAreas.DhRepel.logLogLogDivThreeLeLogDivFive
  refine ⟨1, 1 / 2, one_pos, by norm_num, by norm_num,
    max (max qA (Nat.ceil X)) (Nat.ceil (Real.exp 40)), ?_⟩
  intro q hq _inst χ hχ t ht0 htle
  have hqA' : qA ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have hqX : Nat.ceil X ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have hq40 : Nat.ceil (Real.exp 40) ≤ q := le_trans (le_max_right _ _) hq
  have hXq : X ≤ (q : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hqX)
  have hqex : Real.exp 40 ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil (Real.exp 40)) (by exact_mod_cast hq40)
  have hL40 : (40 : ℝ) ≤ Real.log (q : ℝ) := by
    have h' := Real.log_le_log (Real.exp_pos 40) hqex
    rwa [Real.log_exp] at h'
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  have hq2 : 2 ≤ q := by
    have h41 : (41 : ℝ) ≤ (q : ℝ) :=
      le_trans (by linarith [Real.add_one_le_exp 40] : (41 : ℝ) ≤ Real.exp 40) hqex
    exact_mod_cast (show (2 : ℝ) ≤ (q : ℝ) by linarith)
  -- the base is `≥ 1`
  have hbase1 : (1 : ℝ) ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have h2 : (1 : ℝ) ≤ 10 * Real.log (q : ℝ) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) := mul_le_mul h1 h2 (by norm_num) (by linarith)
  -- the exponent `σ = 1 - t/log q` lies in Jutila's range
  have ht5 : t ≤ Real.log (q : ℝ) / 5 := by
    have := hX (q : ℝ) hXq
    linarith
  have hσ45 : (4 : ℝ) / 5 ≤ 1 - t / Real.log (q : ℝ) := by
    have h1 : t / Real.log (q : ℝ) ≤ (1 : ℝ) / 5 := by
      rw [div_le_iff₀ hlogpos]
      linarith
    linarith
  have hσ1 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
    have : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht0 hlogpos.le
    linarith
  have hT1 : 1 ≤ 10 * Real.log (q : ℝ) := by linarith
  -- the near sum is dominated by the rectangle count, and a single character by the family sum
  calc (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧ Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
      ≤ Work.LinnikAreas.zeroCountIn χ (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)) :=
        Work.LinnikAreas.DhRepel.nearSumLeZeroCountIn hq2 χ t
    _ ≤ ∑ χ' ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ' (1 - t / Real.log (q : ℝ))
            (10 * Real.log (q : ℝ)) :=
        Finset.single_le_sum
          (f := fun χ' => Work.LinnikAreas.zeroCountIn χ' (1 - t / Real.log (q : ℝ))
            (10 * Real.log (q : ℝ)))
          (fun i _ => Work.LinnikAreas.zeroCountIn_nonneg i _ _)
          (Finset.mem_erase.mpr ⟨hχ, Finset.mem_univ χ⟩)
    _ ≤ CJ * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^
          ((2 + (1 / 2 : ℝ)) * (1 - (1 - t / Real.log (q : ℝ)))) :=
        hJ q hq2 (1 - t / Real.log (q : ℝ)) (10 * Real.log (q : ℝ)) hσ45 hσ1 hT1
    _ ≤ CJ * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCJ.le
        refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
        have htL : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht0 hlogpos.le
        have h1σ : 1 - (1 - t / Real.log (q : ℝ)) = t / Real.log (q : ℝ) := by ring
        rw [h1σ, mul_div_assoc]
        nlinarith
    _ ≤ (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) := hqA q hqA' t ht0 htle
    _ = 1 * (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) := (one_mul _).symm


end Work.ZeroFreeTables
