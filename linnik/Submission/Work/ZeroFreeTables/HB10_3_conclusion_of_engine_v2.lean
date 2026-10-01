import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HBLemma10_3_engine_proof
import Submission.Work.ZeroFreeTables.Lemma10_3Cert
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.exists_min_other_wide
import Submission.Work.ZeroFreeTables.exists_min_other_two
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **HB Lemma 10.3, conclusion form** (`λ₃ ≥ 6/7 − 1/1000`), assembled from
the §10 engine `HBLemma10_3_engine` (the case `χ₁χ₂χ₃ = χ₀` of the contradiction),
the remaining cases `HB10_3_Fcases`, and the rational certificate `hcert` at `ε = 1/1000`.

The argument is a minimax one.  Fix `(χ₁, ρ₁)` realising the global minimum `λ₁` over the
wide strip `|Im| ≤ 10`.  If no zero of a character outside `{1, χ₁^{±1}}` lies in the working
region, `Lam3Bound` holds trivially with `χ₂ = 1`.  Otherwise let `(χ₂, ρ₂)` be the
`λ`-minimiser among such zeros.  If some zero of a character outside `{1, χ₁^{±1}, χ₂^{±1}}`
had `λ < 6/7 − 1/1000`, let `(χ₃, ρ₃)` be the corresponding minimiser; then `(χ₁, χ₂, χ₃)`
satisfies the numbering hypotheses of HB §6 with `λ₂ ≤ λ₃ ≤ 6/7`, so either the engine (in
HB's case 3) or the `F`-method cases give `0 ≤ p1014 (λ₁/(6/7)) (1/1000)`, resp.
`6/7 − 1/1000 ≤ max λ₂ λ₃` — both contradicting the certificate and the minimality. -/
theorem HB10_3_conclusion_of_engine_v2 (h3 : Work.ZeroFreeTables.HBLemma10_3_engine)
    (hF : Work.ZeroFreeTables.HB10_3_Fcases)
    (hcert : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → Work.ZeroFreeTables.p1014 δ (1/1000) < 0) :
    Work.ZeroFreeTables.HB10_3_conclusion := by
  obtain ⟨q₃, hq₃⟩ := h3 (1/1000) (by norm_num)
  obtain ⟨qF, hqF⟩ := hF (1/1000) (by norm_num)
  refine ⟨max q₃ qF, ?_⟩
  intro q hq _inst χ₁ ρ₁ hmin
  have hqq₃ : q₃ ≤ q := le_trans (le_max_left _ _) hq
  have hqqF : qF ≤ q := le_trans (le_max_right _ _) hq
  have hχ₁ne1 : χ₁ ≠ 1 := hmin.1.1.1
  have hzm₁ : zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
  -- the working region is non-empty only for `q ≥ 2`
  have hq2 : 2 ≤ q := by
    have hq0 : q ≠ 0 := NeZero.ne q
    by_contra h
    have hq1 : q = 1 := by omega
    subst hq1
    exact hχ₁ne1 (MulChar.ext (fun x => by simp [Subsingleton.elim x 1]))
  by_cases hwit : ∃ (ψ : DirichletCharacter ℂ q) (ρ : ℂ),
      ψ ≠ 1 ∧ ψ ≠ χ₁ ∧ ψ ≠ χ₁⁻¹ ∧ zeroMult ψ ρ ≠ 0 ∧ |ρ.im| ≤ 1
  · -- there is a zero outside the pair `{χ₁^{±1}}`: take the `λ`-minimiser
    obtain ⟨ψ₀, ρ₀, hψ₀, hψ₀₁, hψ₀₁', hzm₀, him₀⟩ := hwit
    obtain ⟨χ₂, ρ₂, hχ₂1, hχ₂χ₁, hχ₂χ₁', hzm₂, him₂, _, hmin₂raw⟩ :=
      exists_min_other_wide 1 (by norm_num) χ₁ ψ₀ ρ₀ hψ₀ hψ₀₁ hψ₀₁' hzm₀ him₀
    have hZ₂ : IsZ χ₂ ρ₂ := ⟨hχ₂1, hzm₂, him₂⟩
    have hmin₂ : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ 1 → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        lamOf q ρ₂ ≤ lamOf q ρ :=
      fun χ ρ hZ hχ1 hχχ₁ hχχ₁' => hmin₂raw χ ρ hχ1 hZ.2.1 hZ.2.2 hχχ₁ hχχ₁'
    refine ⟨χ₂, ?_⟩
    intro χ ρ hZ hχχ₁ hχχ₁' hχχ₂ hχχ₂'
    by_contra hcon
    have hlt : lamOf q ρ < 6/7 - 1/1000 := not_le.mp hcon
    -- a zero outside the two pairs: take the `λ`-minimiser there
    obtain ⟨χ₃, ρ₃, hχ₃1, hχ₃χ₁, hχ₃χ₁', hχ₃χ₂, hχ₃χ₂', hzm₃, him₃, hle₃, hmin₃raw⟩ :=
      exists_min_other_two 1 (by norm_num) χ₁ χ₂ χ ρ hZ.1 hχχ₁ hχχ₁' hχχ₂ hχχ₂' hZ.2.1 hZ.2.2
    have hZ₃ : IsZ χ₃ ρ₃ := ⟨hχ₃1, hzm₃, him₃⟩
    have hmin₃ : ∀ (χ' : DirichletCharacter ℂ q) (ρ' : ℂ), IsZ χ' ρ' → χ' ≠ 1 → χ' ≠ χ₁ →
        χ' ≠ χ₁⁻¹ → χ' ≠ χ₂ → χ' ≠ χ₂⁻¹ → lamOf q ρ₃ ≤ lamOf q ρ' :=
      fun χ' ρ' hZ' hχ1 hχχ₁ hχχ₁' hχχ₂ hχχ₂' =>
        hmin₃raw χ' ρ' hχ1 hZ'.2.1 hZ'.2.2 hχχ₁ hχχ₁' hχχ₂ hχχ₂'
    have hlam₂₃ : lamOf q ρ₂ ≤ lamOf q ρ₃ := hmin₂ χ₃ ρ₃ hZ₃ hχ₃1 hχ₃χ₁ hχ₃χ₁'
    have hlam₃pos : 0 < lamOf q ρ₃ :=
      (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₃1 hzm₃).2.2
    have hlam₃6 : lamOf q ρ₃ ≤ 6/7 := by linarith [hle₃, hlt]
    have hmin₁ : ∀ ρ' : ℂ, IsZ χ₁ ρ' → ρ' ≠ ρ₁ → lamOf q ρ₁ ≤ lamOf q ρ' :=
      fun ρ' hZ' _ => hmin.1.2 χ₁ ρ' hZ'
    by_cases hcase3 : χ₁^2 = 1 ∧ χ₂^2 = 1 ∧ χ₃^2 = 1 ∧ χ₁ * χ₂ * χ₃ = 1 ∧ ρ₁.im = 0
    · -- HB's case 3: the §10 engine produces HB (10.14), contradicting the certificate
      obtain ⟨hsq₁, hsq₂, hsq₃, hprod, him₁⟩ := hcase3
      have hres := hq₃ q hqq₃ χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hmin hsq₁ hsq₂ hsq₃ hprod him₁
        hZ₂ hχ₂χ₁ hχ₂χ₁' hZ₃ hχ₃χ₁ hχ₃χ₁' hχ₃χ₂ hχ₃χ₂'
        hmin₁ hmin₂ hmin₃ hlam₂₃ hlam₃pos hlam₃6
      have hlam₁pos : 0 < lamOf q ρ₁ :=
        (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₁ne1 hzm₁).2.2
      have hδ0 : 0 ≤ lamOf q ρ₁ / (6/7) := div_nonneg hlam₁pos.le (by norm_num)
      have hδ1 : lamOf q ρ₁ / (6/7) ≤ 1 := by
        rw [div_le_one (by norm_num : (0:ℝ) < 6/7)]
        have h1 : lamOf q ρ₁ ≤ lamOf q ρ₃ := hmin.2 χ₃ ρ₃ hχ₃1 hzm₃ (by linarith [him₃])
        linarith [h1, hle₃, hlt]
      have hud : p1014 (lamOf q ρ₁ / (6/7)) (1/1000) < 0 := hcert _ hδ0 hδ1
      linarith
    · -- HB's remaining cases: the `F`-method bound refutes `λ₃ < 6/7 - 1/1000`
      have hres := hqF q hqqF χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hmin
        hZ₂ hχ₂χ₁ hχ₂χ₁' hZ₃ hχ₃χ₁ hχ₃χ₁' hχ₃χ₂ hχ₃χ₂' hcase3
      have hmax : max (lamOf q ρ₂) (lamOf q ρ₃) ≤ lamOf q ρ₃ := by
        rw [max_le_iff]; exact ⟨hlam₂₃, le_rfl⟩
      linarith [hres, hmax, hle₃, hlt]
  · -- no zero outside `{1, χ₁^{±1}}` lies in the region: `χ₂ = 1` works vacuously
    refine ⟨1, ?_⟩
    intro χ ρ hZ hχχ₁ hχχ₁' hχχ₂ hχχ₂'
    exfalso
    exact hwit ⟨χ, ρ, hZ.1, hχχ₁, hχχ₁', hZ.2.1, hZ.2.2⟩

end Work.ZeroFreeTables
