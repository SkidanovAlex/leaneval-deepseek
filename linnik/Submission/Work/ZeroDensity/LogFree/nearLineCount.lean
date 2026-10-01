import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.ZFImports
import Submission.Work.ZeroDensity.LogFree.excZeroReal
import Submission.Work.ZeroDensity.LogFree.excCharUnique

namespace Work.ZeroDensity.LogFree

/-- `Work.ZeroDensity.LogFree.NearLineCount p` (defined in `Submission/Work/ZeroDensity/LogFree/GramProps.lean`): there are `c₁ > 0` and `K ≥ 0` such that every `1/𝓛`-separated system of non-principal zeros with `λ(ρ) = (1-Re ρ)·Lscale q T ≤ c₁` in the strip `p.σ₀ ≤ Re ρ < 1`, `|Im ρ| ≤ T` has cardinality at most `K`. Route: take `c₁` below the constant of `Work.ZeroDensity.LogFree.excZeroReal` (the threshold of the uniform zero-free regions `LFunction_zeroFree_offAxis_uniform` and `LFunction_zeroFree_uniform_realAxis`), so each such zero is real and its primitive character is real; `Work.ZeroDensity.LogFree.excCharUnique` (with Landau's two-real-zero repulsion `Work.LinnikAreas.OtherCharRepel.twoRealCharRepel`, whose threshold is `q ≥ 9`) then shows at most one character carries such a zero when `q ≥ 9`, while for `q ≤ 8` one has `m ≤ q`; so `K = 9` works. The separation hypothesis (with `1/Lscale q T > 0`) rules out two distinct real zeros of the *same* character. -/
theorem nearLineCount (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.NearLineCount p := by
  -- the two inputs: zeros that close to the line are real zeros of real characters
  -- (uniform zero-free regions), and at most one character mod `q` carries such a zero
  -- for `q` beyond the repulsion threshold
  obtain ⟨c₀, hc₀pos, h₀⟩ := excZeroReal
  obtain ⟨c, hcpos, q₀, hq₀⟩ := excCharUnique
  refine ⟨min c₀ c / 2, div_pos (lt_min hc₀pos hcpos) (by norm_num),
    ((max q₀ 1 : ℕ) : ℝ), by positivity, 1, by norm_num, ?_⟩
  intro q hqI hq T σ hT hD hσ0 m χ ρ hχ1 hzm hσ hρ1 him hsmall hsep
  -- the logarithmic parameter is positive
  have hLpos : 0 < Lscale q T := by
    rw [Lscale, scale]
    apply Real.log_pos
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqI
    nlinarith
  -- the threshold `min c₀ c / 2` lies strictly below both thresholds
  have hltc₀ : min c₀ c / 2 < c₀ := by
    have h1 : min c₀ c ≤ c₀ := min_le_left _ _
    linarith
  have hltc : min c₀ c / 2 < c := by
    have h1 : min c₀ c ≤ c := min_le_right _ _
    linarith
  -- every zero of the system is real, by the uniform zero-free region off the axis
  have him0 : ∀ i, (ρ i).im = 0 := fun i =>
    (h₀ q hqI (χ i) (hχ1 i) (ρ i) T hT (him i) (hzm i)
      (lt_of_le_of_lt (hsmall i) hltc₀)).1
  by_cases hcase : q₀ ≤ q
  · -- beyond the repulsion threshold at most one character carries such a zero,
    -- and two real zeros of the same character are excluded by the separation hypothesis
    have hall : ∀ i j, χ i = χ j := by
      intro i j
      by_contra hne
      exact hq₀ q hcase T hT (χ i) (χ j) (hχ1 i) (hχ1 j) hne
        ⟨⟨ρ i, hzm i, him i, lt_of_le_of_lt (hsmall i) hltc⟩,
         ⟨ρ j, hzm j, him j, lt_of_le_of_lt (hsmall j) hltc⟩⟩
    have hm1 : m ≤ 1 := by
      by_contra h
      have hm2 : 2 ≤ m := by omega
      set i0 : Fin m := ⟨0, by omega⟩ with hi0
      set i1 : Fin m := ⟨1, by omega⟩ with hi1
      have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
      have hse := hsep i0 i1 hne (hall i0 i1)
      have h0 : |(ρ i0).im - (ρ i1).im| = 0 := by rw [him0 i0, him0 i1]; norm_num
      rw [h0] at hse
      have hpos : 0 < 1 / Lscale q T := one_div_pos.mpr hLpos
      linarith
    calc (m : ℝ) ≤ 1 := by exact_mod_cast hm1
      _ ≤ ((max q₀ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right q₀ 1
  · -- below the repulsion threshold the separation hypothesis makes `χ` injective,
    -- and there are at most `q ≤ q₀` characters mod `q`
    have hcase' : q < q₀ := not_le.mp hcase
    have hinj : Function.Injective χ := by
      intro i j hij
      by_contra hne
      have hse := hsep i j hne hij
      have h0 : |(ρ i).im - (ρ j).im| = 0 := by rw [him0 i, him0 j]; norm_num
      rw [h0] at hse
      have hpos : 0 < 1 / Lscale q T := one_div_pos.mpr hLpos
      linarith
    have hcard : Fintype.card (Fin m) ≤ Fintype.card (DirichletCharacter ℂ q) :=
      Fintype.card_le_of_injective χ hinj
    have hqb : Fintype.card (DirichletCharacter ℂ q) ≤ q := by
      rw [← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
      exact Nat.totient_le q
    have hm : m ≤ q := by simpa using le_trans hcard hqb
    have hmle : (m : ℝ) < ((max q₀ 1 : ℕ) : ℝ) := by
      calc (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hm
        _ < (q₀ : ℝ) := by exact_mod_cast hcase'
        _ ≤ ((max q₀ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left q₀ 1
    exact le_of_lt hmle

end Work.ZeroDensity.LogFree
