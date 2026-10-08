import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma24
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_lemma21Ext
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.thm32

/-!
# Area BG: Bender–Glauberman 1981, Lemma 3.3, case `|S| ≥ 8`

`Work.BG.lemma33Case2` is the `|S| ≥ 8` branch (`4 ≤ D.n`) of BG Lemma 3.3: there is **no**
`χ ∈ ±Irr(G)` whose support `𝒮(χ) = bset C f χ` contains three distinct `s`-fixed characters
`ν` with `|Λν| = m = D.n`.

The route is the paper's counting identity of Theorem 3.2 (`Work.BG.chi_sum_T_eq`):

  `Σ_{g ∈ T} |χ(g)|² = |H₀| · (|𝒮(χ)| - Ssum)`,   `Ssum = Σ_ν e_ν² (1 + c_ν) / |Λν|`,

together with the strict TI-counting bound `Σ_{g ∈ T}|χ(g)|² < 2 |H₀|`
(`Work.BG.sum_TfinH_normSq_lt`) and `|𝒮(χ)| ≤ 3` (`Work.BG.thm32`).  Three distinct members
force `|𝒮(χ)| = 3`, so `Ssum = 3/D.n` and the identity reads

  `|H₀| · (3 - 3/D.n) = Σ_{g ∈ T}|χ(g)|² < 2 |H₀|`,

i.e. `3/D.n > 1`, contradicting `4 ≤ D.n`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## 1. Pigeonhole for `𝒮(χ)` -/

/-- If `𝒮(χ) = bset C f χ` has at most three elements and contains three distinct irreducible
characters `e₁, e₂, e₃`, then it has exactly three elements and every irreducible member of it
is one of the three. -/
theorem bset_classify_of_three (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (e₁ e₂ e₃ : IrreducibleCharacter ↥C.P.H0)
    (h₁ : (e₁ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h₂ : (e₂ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h₃ : (e₃ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hle : (bset C f χ).ncard ≤ 3) :
    (bset C f χ).ncard = 3 ∧
      ∀ ν : IrreducibleCharacter ↥C.P.H0, (ν : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ →
        ν = e₁ ∨ ν = e₂ ∨ ν = e₃ := by
  classical
  have hfin := s02_bset_finite C f χ
  have hcl12 : (e₁ : ClassFunction ↥C.P.H0 ℂ) ≠ (e₂ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => h12 (Subtype.ext_iff.mpr h)
  have hcl13 : (e₁ : ClassFunction ↥C.P.H0 ℂ) ≠ (e₃ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => h13 (Subtype.ext_iff.mpr h)
  have hcl23 : (e₂ : ClassFunction ↥C.P.H0 ℂ) ≠ (e₃ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => h23 (Subtype.ext_iff.mpr h)
  have hsub : ({(e₁ : ClassFunction ↥C.P.H0 ℂ), (e₂ : ClassFunction ↥C.P.H0 ℂ),
      (e₃ : ClassFunction ↥C.P.H0 ℂ)} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact h₁
    · rw [h]; exact h₂
    · rw [h]; exact h₃
  have hcard3 : ({(e₁ : ClassFunction ↥C.P.H0 ℂ), (e₂ : ClassFunction ↥C.P.H0 ℂ),
      (e₃ : ClassFunction ↥C.P.H0 ℂ)} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hcl12, hcl13]),
      Set.ncard_insert_of_notMem (by simp [hcl23]), Set.ncard_singleton]
  have h3le : 3 ≤ (bset C f χ).ncard := by
    have h := Set.ncard_le_ncard hsub hfin
    omega
  refine ⟨le_antisymm hle h3le, ?_⟩
  intro ν hν
  by_cases hc1 : ν = e₁
  · exact Or.inl hc1
  by_cases hc2 : ν = e₂
  · exact Or.inr (Or.inl hc2)
  by_cases hc3 : ν = e₃
  · exact Or.inr (Or.inr hc3)
  exfalso
  have hcl1 : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ (e₁ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => hc1 (Subtype.ext_iff.mpr h)
  have hcl2 : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ (e₂ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => hc2 (Subtype.ext_iff.mpr h)
  have hcl3 : (ν : ClassFunction ↥C.P.H0 ℂ) ≠ (e₃ : ClassFunction ↥C.P.H0 ℂ) :=
    fun h => hc3 (Subtype.ext_iff.mpr h)
  have hsub' : ({(ν : ClassFunction ↥C.P.H0 ℂ), (e₁ : ClassFunction ↥C.P.H0 ℂ),
      (e₂ : ClassFunction ↥C.P.H0 ℂ), (e₃ : ClassFunction ↥C.P.H0 ℂ)} :
        Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact hν
    · rw [h]; exact h₁
    · rw [h]; exact h₂
    · rw [h]; exact h₃
  have h4 := Set.ncard_le_ncard hsub' hfin
  have hcard4 : ({(ν : ClassFunction ↥C.P.H0 ℂ), (e₁ : ClassFunction ↥C.P.H0 ℂ),
      (e₂ : ClassFunction ↥C.P.H0 ℂ), (e₃ : ClassFunction ↥C.P.H0 ℂ)} :
        Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hcl1, hcl2, hcl3]),
      Set.ncard_insert_of_notMem (by simp [hcl12, hcl13]),
      Set.ncard_insert_of_notMem (by simp [hcl23]), Set.ncard_singleton]
  omega

/-! ## 2. The correction term `Ssum` when `𝒮(χ)` consists of three `s`-fixed characters -/

/-- **`Ssum` for three maximal `s`-fixed members.**  If `𝒮(χ)` contains three distinct
`s`-fixed characters `eᵢ` with `|Λeᵢ| = n` and `|𝒮(χ)| ≤ 3`, then the correction term of the
counting identity of Theorem 3.2 is `Ssum = 3/n`. -/
theorem Ssum_eq_three_div (D : BGData G) (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (e₁ e₂ e₃ : IrreducibleCharacter ↥C.P.H0)
    (h₁ : (e₁ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h₂ : (e₂ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h₃ : (e₃ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hs1 : sconj C (e₁ : ClassFunction ↥C.P.H0 ℂ) = (e₁ : ClassFunction ↥C.P.H0 ℂ))
    (hs2 : sconj C (e₂ : ClassFunction ↥C.P.H0 ℂ) = (e₂ : ClassFunction ↥C.P.H0 ℂ))
    (hs3 : sconj C (e₃ : ClassFunction ↥C.P.H0 ℂ) = (e₃ : ClassFunction ↥C.P.H0 ℂ))
    (ho1 : (lamOrbit C (e₁ : ClassFunction ↥C.P.H0 ℂ)).ncard = D.n)
    (ho2 : (lamOrbit C (e₂ : ClassFunction ↥C.P.H0 ℂ)).ncard = D.n)
    (ho3 : (lamOrbit C (e₃ : ClassFunction ↥C.P.H0 ℂ)).ncard = D.n)
    (hle : (bset C f χ).ncard ≤ 3) :
    Ssum C f χ = (((3 : ℝ) / (D.n : ℝ) : ℝ) : ℂ) := by
  classical
  obtain ⟨-, hclass⟩ :=
    bset_classify_of_three C f χ e₁ e₂ e₃ h₁ h₂ h₃ h12 h13 h23 hle
  have hc1 : cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs1 hh.2
    · rfl
  have hc2 : cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs2 hh.2
    · rfl
  have hc3 : cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ) = 0 := by
    rw [cOrbitR]
    split_ifs with hh
    · exact absurd hs3 hh.2
    · rfl
  have hv1 : bsetInd C f χ e₁ * (1 + cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₁ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / (D.n : ℝ) := by
    rw [bsetInd_of_mem h₁, hc1, ho1]
    norm_num
  have hv2 : bsetInd C f χ e₂ * (1 + cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₂ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / (D.n : ℝ) := by
    rw [bsetInd_of_mem h₂, hc2, ho2]
    norm_num
  have hv3 : bsetInd C f χ e₃ * (1 + cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ)) /
      ((lamOrbit C (e₃ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 1 / (D.n : ℝ) := by
    rw [bsetInd_of_mem h₃, hc3, ho3]
    norm_num
  have hterm : Ssum C f χ = (((∑ ν : IrreducibleCharacter ↥C.P.H0,
      bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
        ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) : ℝ) : ℂ) := by
    rw [Ssum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun ν _ => Ssum_term_ofReal C f hf χ hχ ν
  have hF : (∑ ν : IrreducibleCharacter ↥C.P.H0,
      bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
        ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) = 3 / (D.n : ℝ) := by
    have hzero : ∀ ν : IrreducibleCharacter ↥C.P.H0,
        ν ∉ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)) →
        bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) = 0 := by
      intro ν hν
      have hmem : (ν : ClassFunction ↥C.P.H0 ℂ) ∉ bset C f χ := by
        intro hb
        rcases hclass ν hb with h | h | h
        · exact hν (by simp [h])
        · exact hν (by simp [h])
        · exact hν (by simp [h])
      rw [bsetInd_of_notMem (ν := ν) hmem]
      ring
    have hsum_eq : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
          ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) =
        ∑ ν ∈ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)),
          bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) :=
      (Finset.sum_subset (Finset.subset_univ _) (fun ν _ hν => hzero ν hν)).symm
    have hthree : (∑ ν ∈ ({e₁, e₂, e₃} : Finset (IrreducibleCharacter ↥C.P.H0)),
          bsetInd C f χ ν * (1 + cOrbitR C (ν : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (ν : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ)) =
        bsetInd C f χ e₁ * (1 + cOrbitR C (e₁ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₁ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) +
          (bsetInd C f χ e₂ * (1 + cOrbitR C (e₂ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₂ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ) +
          (bsetInd C f χ e₃ * (1 + cOrbitR C (e₃ : ClassFunction ↥C.P.H0 ℂ)) /
            ((lamOrbit C (e₃ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℝ))) := by
      rw [Finset.sum_insert (show e₁ ∉ ({e₂, e₃} : Finset _) by simp [h12, h13]),
        Finset.sum_insert (show e₂ ∉ ({e₃} : Finset _) by simp [h23]), Finset.sum_singleton]
    rw [hsum_eq, hthree, hv1, hv2, hv3]
    ring
  rw [hterm, hF]

/-! ## 3. The counting identity in real form -/

/-- **Theorem 3.2 identity for three members.**  With `|𝒮(χ)| = 3` and `Ssum = 3/n`,

  `Σ_{g ∈ T} |χ(g)|² = |H₀| · (3 - 3/n)`. -/
theorem sum_TfinH_normSq_eq_of_three (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    (hcard : (bset C f χ).ncard = 3)
    (hSsum : Ssum C f χ = (((3 : ℝ) / (D.n : ℝ) : ℝ) : ℂ)) :
    (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) = (Nat.card ↥C.P.H0 : ℝ) * (3 - 3 / (D.n : ℝ)) := by
  classical
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hC := chi_sum_T_eq D C hDC f hf χ hχ
  have hL : (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G))) =
      Complex.ofReal (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj (χ (g : G))
  have h3c : ((3 : ℕ) : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
  have hR : (Nat.card ↥C.P.H0 : ℂ) * (((bset C f χ).ncard : ℂ) - Ssum C f χ) =
      Complex.ofReal ((Nat.card ↥C.P.H0 : ℝ) * (3 - 3 / (D.n : ℝ))) := by
    rw [hcard, hSsum, h3c, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul]
  exact Complex.ofReal_inj.mp (hL.symm.trans (hC.trans hR))

/-! ## 4. Lemma 3.3 (`|S| ≥ 8` branch) -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma33Case2 {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ → 4 ≤ D.n →
    ∀ ν₁ ∈ Work.GW2.C16.bset C f χ, ∀ ν₂ ∈ Work.GW2.C16.bset C f χ,
      ∀ ν₃ ∈ Work.GW2.C16.bset C f χ,
    ν₁ ≠ ν₂ → ν₁ ≠ ν₃ → ν₂ ≠ ν₃ →
    Work.BG.sconj C ν₁ = ν₁ → Work.BG.sconj C ν₂ = ν₂ → Work.BG.sconj C ν₃ = ν₃ →
    (Work.BG.lamOrbit C ν₁).ncard = D.n → (Work.BG.lamOrbit C ν₂).ncard = D.n →
      (Work.BG.lamOrbit C ν₃).ncard = D.n →
    False := by
  intro hDC hS3 f hf χ hχ hn ν₁ hν₁ ν₂ hν₂ ν₃ hν₃ h12 h13 h23 hs1 hs2 hs3 ho1 ho2 ho3
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  -- `|𝒮(χ)| ≤ 3` (Theorem 3.2), and three members force `|𝒮(χ)| = 3`
  have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hne12 : (⟨ν₁, hν₁.1⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨ν₂, hν₂.1⟩ :=
    fun h => h12 (Subtype.ext_iff.mp h)
  have hne13 : (⟨ν₁, hν₁.1⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨ν₃, hν₃.1⟩ :=
    fun h => h13 (Subtype.ext_iff.mp h)
  have hne23 : (⟨ν₂, hν₂.1⟩ : IrreducibleCharacter ↥C.P.H0) ≠ ⟨ν₃, hν₃.1⟩ :=
    fun h => h23 (Subtype.ext_iff.mp h)
  have hcard : (bset C f χ).ncard = 3 :=
    (bset_classify_of_three C f χ ⟨ν₁, hν₁.1⟩ ⟨ν₂, hν₂.1⟩ ⟨ν₃, hν₃.1⟩
      hν₁ hν₂ hν₃ hne12 hne13 hne23 hle).1
  have hSsum : Ssum C f χ = (((3 : ℝ) / (D.n : ℝ) : ℝ) : ℂ) :=
    Ssum_eq_three_div D C f hf χ hχ ⟨ν₁, hν₁.1⟩ ⟨ν₂, hν₂.1⟩ ⟨ν₃, hν₃.1⟩
      hν₁ hν₂ hν₃ hne12 hne13 hne23 hs1 hs2 hs3 ho1 ho2 ho3 hle
  -- the identity, in real form
  have hreal := sum_TfinH_normSq_eq_of_three D C hDC f hf χ hχ hcard hSsum
  have hlt := sum_TfinH_normSq_lt C χ hχ
  rw [hreal] at hlt
  -- arithmetic
  have hH0 : (0 : ℝ) < (Nat.card ↥C.P.H0 : ℝ) := by exact_mod_cast Nat.card_pos
  have hkey : (Nat.card ↥C.P.H0 : ℝ) * (3 - 3 / (D.n : ℝ)) <
      (Nat.card ↥C.P.H0 : ℝ) * 2 := by linarith
  have hlt' : 3 - 3 / (D.n : ℝ) < 2 :=
    lt_of_mul_lt_mul_left hkey (le_of_lt hH0)
  have hn4 : (4 : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hn
  have hbound : 3 / (D.n : ℝ) ≤ 3 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn4
  linarith

end Work.BG
