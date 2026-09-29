/-
# The multivariate vanishing filtration: the counting theorem (Lemma `total jumps`)

This module completes the paper's §"Filtered evaluation modules": for a finite-dimensional
`ℝ`-subspace `V ⊆ ℝ⟦x₁,…,x_d⟧` (an `MvPowerSeries`), the number of *leading exponents*

`𝒱 = {leadExp f : f ∈ V, f ≠ 0}`

(with `leadExp` the `≺`-minimal exponent of the support, total degree first and lexicographic second)
is exactly `finrank ℝ V`.  This is the paper's Lemma `total jumps`.

The proof is the pivot argument of linear algebra, applied level by level:

* `lvlCoeff V N : ↥(degStep V N) →ₗ[ℝ] (lvlIx σ N → ℝ)` is the degree-`N` coefficient vector of an
  element of the `N`-th degree step (indexed by the exponents of total degree `N`, ordered
  lexicographically via `Lex`);
* `pivotSet V N` is the set of pivots of its range, and the linear-algebra pivot lemma
  `Commons.LinearAlgebra.pivot_ncard_eq_finrank` gives `(pivotSet V N).ncard = finrank (range)`;
* `ncard_jumpFinset_eq_pivotSet` identifies the pivots of level `N` with the leading exponents of
  total degree `N` (`mem_pivotSet_iff`), using `minDeg`, `leadExp` and `dk`;
* the kernel of `lvlCoeff V N` is the `(N+1)`-st degree step (`kerEquiv`), so rank-nullity gives
  `#(degree-`N` leading exponents) = finrank (degStep V N) - finrank (degStep V (N+1))`
  (`card_jumpFinset_eq`);
* the degree filtration is separated (`exists_degStep_eq_bot`), so telescoping over `N` gives the
  result (`ncard_jumpSet_eq_finrank`).
-/
import Mathlib
import Submission.CDT.MvVanishing
import Submission.Commons.LinearAlgebra.pivot_ncard_eq_finrank

open MvPowerSeries
open scoped BigOperators

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false


namespace Submission.CDT.MvVanishing

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]

/-- The exponent vectors of total degree `N`, indexed by the lex order `≺`. -/
abbrev lvlIx (σ : Type*) [Fintype σ] [DecidableEq σ] [LinearOrder σ] (N : ℕ) : Type _ :=
  {n : Lex (σ →₀ ℕ) // ofLex n ∈ degLevel N}

noncomputable instance lvlFintype (N : ℕ) : Fintype (lvlIx σ N) :=
  Fintype.ofEquiv {s : σ →₀ ℕ // s ∈ degLevel N}
    (Equiv.subtypeEquiv toLex (fun _ => Iff.rfl)).symm

/-- The degree-`N` coefficient vector of an element of the `N`-th degree step. -/
noncomputable def lvlCoeff (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) :
    ↥(degStep V N) →ₗ[ℝ] (lvlIx σ N → ℝ) :=
  LinearMap.pi fun s : lvlIx σ N =>
    (MvPowerSeries.coeff (ofLex (s : Lex (σ →₀ ℕ)))).comp (Submodule.subtype _)

theorem lvlCoeff_apply (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) (g : ↥(degStep V N))
    (s : lvlIx σ N) :
    lvlCoeff V N g s =
      (MvPowerSeries.coeff (ofLex (s : Lex (σ →₀ ℕ)))) (g : MvPowerSeries σ ℝ) := rfl

/-- The pivots of the degree-`N` coefficient space of `V`: the leading exponents of total degree
`N` of the elements of `V`. -/
def pivotSet (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) : Set (lvlIx σ N) :=
  {s | ∃ f ∈ (lvlCoeff V N).range, f s ≠ 0 ∧ ∀ m : lvlIx σ N, m < s → f m = 0}

/-- The set of "leading exponent keys" of total degree `N` occurring in `V`. -/
noncomputable def jumpFinset (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) :
    Finset (Lex (ℕ × Lex (σ →₀ ℕ))) :=
  ((degLevel N).filter (fun s => ∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧
      leadExp f hf = dk s)).image dk

theorem mem_jumpFinset_dk {V : Submodule ℝ (MvPowerSeries σ ℝ)} {N : ℕ} {s : σ →₀ ℕ} :
    dk s ∈ jumpFinset V N ↔ s ∈ degLevel N ∧
      ∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧ leadExp f hf = dk s := by
  constructor
  · intro h
    obtain ⟨s', hs', hss'⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hs'
    rw [dk_injective hss'] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨hs, h2⟩
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, h2⟩, rfl⟩

theorem mem_jumpFinset {V : Submodule ℝ (MvPowerSeries σ ℝ)} {N : ℕ}
    {key : Lex (ℕ × Lex (σ →₀ ℕ))} :
    key ∈ jumpFinset V N ↔ ∃ s : σ →₀ ℕ, s ∈ degLevel N ∧
      (∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧ leadExp f hf = dk s) ∧ dk s = key := by
  constructor
  · intro h
    obtain ⟨s', hs', hss'⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hs'
    exact ⟨s', h1, h2, hss'⟩
  · rintro ⟨s, hs, h2, hsk⟩
    rw [← hsk]
    exact mem_jumpFinset_dk.mpr ⟨hs, h2⟩

/-! ## The degree filtration is separated -/

theorem finite_degStep (V : Submodule ℝ (MvPowerSeries σ ℝ)) [Module.Finite ℝ V] (N : ℕ) :
    Module.Finite ℝ ↥(degStep V N) :=
  Module.Finite.of_injective (Submodule.inclusion (degStep_le V N)) (Submodule.inclusion_injective _)

theorem exists_degStep_eq_bot (V : Submodule ℝ (MvPowerSeries σ ℝ)) [Module.Finite ℝ V] :
    ∃ N, degStep V N = ⊥ := by
  have hAnti : Antitone fun n => Module.finrank ℝ ↥(degStep V n) := by
    intro m n hmn
    have := finite_degStep V m
    exact Submodule.finrank_mono (degStep_antitone V hmn)
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n →
      Module.finrank ℝ ↥(degStep V n) = Module.finrank ℝ ↥(degStep V N) := by
    have hne : (Set.range fun n => Module.finrank ℝ ↥(degStep V n)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨N, hN⟩ := Nat.sInf_mem hne
    have hN' : Module.finrank ℝ ↥(degStep V N) =
        sInf (Set.range fun n => Module.finrank ℝ ↥(degStep V n)) := hN
    refine ⟨N, fun n hn => ?_⟩
    have h1 : Module.finrank ℝ ↥(degStep V n) ≤ Module.finrank ℝ ↥(degStep V N) := hAnti hn
    have h2 : Module.finrank ℝ ↥(degStep V N) ≤ Module.finrank ℝ ↥(degStep V n) := by
      rw [hN']; exact Nat.sInf_le ⟨n, rfl⟩
    exact le_antisymm h1 h2
  have hEq : ∀ n, N ≤ n → degStep V n = degStep V N := by
    intro n hn
    have := finite_degStep V N
    exact Submodule.eq_of_le_of_finrank_eq (degStep_antitone V hn) (hN n hn)
  refine ⟨N, le_antisymm (fun f hf => ?_) bot_le⟩
  rw [Submodule.mem_bot]
  refine MvPowerSeries.ext fun s => ?_
  have hmem : f ∈ degStep V (max N (tdeg s + 1)) := by
    rw [hEq _ (le_max_left _ _)]
    exact hf
  simpa using (mem_degStep.mp hmem).2 s (by omega)

/-! ## The pivot/jump correspondence at a fixed degree level -/

theorem jump_of_pivot (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) {n : lvlIx σ N}
    (hn : n ∈ pivotSet V N) :
    ∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧
      leadExp f hf = dk (ofLex (n : Lex (σ →₀ ℕ))) := by
  obtain ⟨f, hfmem, hf0, hvan⟩ := hn
  obtain ⟨g, rfl⟩ := hfmem
  have hgmem : (g : MvPowerSeries σ ℝ) ∈ degStep V N := g.2
  have hgV : (g : MvPowerSeries σ ℝ) ∈ V := (mem_degStep.mp hgmem).1
  have hc : (MvPowerSeries.coeff (ofLex (n : Lex (σ →₀ ℕ)))) (g : MvPowerSeries σ ℝ) ≠ 0 := by
    rw [← lvlCoeff_apply]; exact hf0
  have hg0 : (g : MvPowerSeries σ ℝ) ≠ 0 := fun h => hc (by rw [h]; simp)
  have htdeg : tdeg (ofLex (n : Lex (σ →₀ ℕ))) = N := mem_degLevel_iff.mp n.2
  refine ⟨g, hg0, hgV, ?_⟩
  have hmin1 : minDeg (g : MvPowerSeries σ ℝ) hg0 ≤ tdeg (ofLex (n : Lex (σ →₀ ℕ))) :=
    minDeg_le _ hg0 hc
  have hmin2 : N ≤ minDeg (g : MvPowerSeries σ ℝ) hg0 :=
    (mem_degStep_iff_minDeg V hgV hg0).mp hgmem
  have hmin : minDeg (g : MvPowerSeries σ ℝ) hg0 = N := le_antisymm (by omega) hmin2
  set t := udk (leadExp (g : MvPowerSeries σ ℝ) hg0) with ht
  have htdeg' : tdeg t = N := by rw [ht, tdeg_leadExp, hmin]
  have hct : (MvPowerSeries.coeff t) (g : MvPowerSeries σ ℝ) ≠ 0 := coeff_leadExp_ne_zero _ hg0
  have hle : leadExp (g : MvPowerSeries σ ℝ) hg0 ≤ dk (ofLex (n : Lex (σ →₀ ℕ))) :=
    leadExp_le _ hg0 hc (by rw [htdeg, hmin])
  have hle' : toLex t ≤ (n : Lex (σ →₀ ℕ)) := by
    have h0 : dk t ≤ dk (ofLex (n : Lex (σ →₀ ℕ))) := by
      rw [ht, dk_udk_leadExp]; exact hle
    have h := (dk_le_iff t (ofLex (n : Lex (σ →₀ ℕ)))).mp h0
    rcases h with h | ⟨-, hlex⟩
    · rw [htdeg', htdeg] at h; exact absurd h (lt_irrefl N)
    · rwa [toLex_ofLex] at hlex
  have hge : (n : Lex (σ →₀ ℕ)) ≤ toLex t := by
    by_contra hcon
    push Not at hcon
    have hv := hvan (⟨toLex t,
      (mem_degLevel_iff.mpr htdeg' : ofLex (toLex t) ∈ degLevel N)⟩ : lvlIx σ N) hcon
    rw [lvlCoeff_apply, ofLex_toLex] at hv
    exact hct hv
  have heq : toLex t = (n : Lex (σ →₀ ℕ)) := le_antisymm hle' hge
  have h0 : dk t ≤ dk (ofLex (n : Lex (σ →₀ ℕ))) := by
    have h := (dk_le_iff t (ofLex (n : Lex (σ →₀ ℕ)))).mpr (Or.inr ⟨by rw [htdeg', htdeg], hle'⟩)
    exact h
  have heqdk : dk t = dk (ofLex (n : Lex (σ →₀ ℕ))) := by
    refine le_antisymm h0 ?_
    refine (dk_le_iff (ofLex (n : Lex (σ →₀ ℕ))) t).mpr (Or.inr ⟨?_, ?_⟩)
    · rw [htdeg, htdeg']
    · rwa [toLex_ofLex]
  have h1 : dk t = leadExp (g : MvPowerSeries σ ℝ) hg0 := by rw [ht, dk_udk_leadExp]
  rw [← h1, heqdk]

theorem pivot_of_jump_aux (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) {s : σ →₀ ℕ}
    (hs : s ∈ degLevel N) (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) (hfV : f ∈ V)
    (hlead : leadExp f hf = dk s) :
    (⟨toLex s, (hs : ofLex (toLex s) ∈ degLevel N)⟩ : lvlIx σ N) ∈ pivotSet V N := by
  have htdeg : tdeg s = N := mem_degLevel_iff.mp hs
  have hmin : minDeg f hf = N := by
    rw [← tdeg_leadExp f hf, hlead, udk_dk, htdeg]
  have hgmem : f ∈ degStep V N := by
    refine mem_degStep.mpr ⟨hfV, fun t ht => ?_⟩
    by_contra hc
    exact absurd (minDeg_le f hf hc) (by rw [hmin]; omega)
  refine ⟨lvlCoeff V N ⟨f, hgmem⟩, ⟨⟨f, hgmem⟩, rfl⟩, ?_, ?_⟩
  · rw [lvlCoeff_apply, ofLex_toLex]
    have h2 := coeff_leadExp_ne_zero f hf
    rw [hlead, udk_dk] at h2
    exact h2
  · intro m hm
    rw [lvlCoeff_apply]
    by_contra hc
    have hle := leadExp_le_of_coeff_ne_zero f hf hc
    have hlt : dk (ofLex (m : Lex (σ →₀ ℕ))) < dk s := by
      refine (dk_lt_iff _ _).mpr (Or.inr ⟨?_, ?_⟩)
      · rw [mem_degLevel_iff.mp m.2, htdeg]
      · show (m : Lex (σ →₀ ℕ)) < toLex s
        exact hm
    rw [hlead] at hle
    exact absurd hle (not_le.mpr hlt)

theorem pivot_of_jump (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) {s : lvlIx σ N}
    (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) (hfV : f ∈ V)
    (hlead : leadExp f hf = dk (ofLex (s : Lex (σ →₀ ℕ)))) : s ∈ pivotSet V N := by
  have h := pivot_of_jump_aux V N s.2 f hf hfV hlead
  convert h using 1
  exact Subtype.ext (by simp)

/-- **The pivot condition at level `N` is the leading-exponent condition.** -/
theorem mem_pivotSet_iff (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) (s : lvlIx σ N) :
    s ∈ pivotSet V N ↔ ∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧
      leadExp f hf = dk (ofLex (s : Lex (σ →₀ ℕ))) :=
  ⟨fun h => jump_of_pivot V N h, fun ⟨f, hf, hfV, hlead⟩ => pivot_of_jump V N f hf hfV hlead⟩

/-- The pivots of the `N`-th level are exactly the degree-`N` leading exponents of `V`. -/
theorem ncard_jumpFinset_eq_pivotSet (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) :
    (↑(jumpFinset V N) : Set (Lex (ℕ × Lex (σ →₀ ℕ)))).ncard = (pivotSet V N).ncard := by
  have hmap : ∀ key ∈ (↑(jumpFinset V N) : Set (Lex (ℕ × Lex (σ →₀ ℕ)))),
      ofLex (toLex (udk key) : Lex (σ →₀ ℕ)) ∈ degLevel N := by
    intro key hk
    obtain ⟨s, hs, -, hkey⟩ := mem_jumpFinset.mp hk
    rw [← hkey, udk_dk]
    exact hs
  refine Set.ncard_congr (fun key hk => (⟨toLex (udk key), hmap key hk⟩ : lvlIx σ N)) ?_ ?_ ?_
  · intro key hk
    rw [mem_pivotSet_iff]
    simp only [ofLex_toLex]
    obtain ⟨s, hs, ⟨f, hf, hfV, hlead⟩, hkey⟩ := mem_jumpFinset.mp hk
    have h1 : udk key = s := by rw [← hkey, udk_dk]
    rw [h1]
    exact ⟨f, hf, hfV, hlead⟩
  · intro key₁ key₂ hk₁ hk₂ heq
    obtain ⟨s₁, -, -, hkey₁⟩ := mem_jumpFinset.mp hk₁
    obtain ⟨s₂, -, -, hkey₂⟩ := mem_jumpFinset.mp hk₂
    have h1 : toLex (udk key₁) = toLex (udk key₂) := by
      have := congrArg (fun x : lvlIx σ N => (x : Lex (σ →₀ ℕ))) heq
      simpa using this
    have h2 : udk key₁ = udk key₂ := by
      have := congrArg ofLex h1
      simpa using this
    rw [← hkey₁, ← hkey₂, udk_dk, udk_dk] at h2
    rw [← hkey₁, ← hkey₂, h2]
  · intro n hn
    rw [mem_pivotSet_iff] at hn
    obtain ⟨f, hf, hfV, hlead⟩ := hn
    refine ⟨dk (ofLex (n : Lex (σ →₀ ℕ))),
      mem_jumpFinset_dk.mpr ⟨n.2, f, hf, hfV, hlead⟩, ?_⟩
    apply Subtype.ext
    simp only [udk_dk, toLex_ofLex]

/-! ## The dimension drop at a level -/

/-- The kernel of the `N`-th level coefficient map is the `N+1`-st step of the degree
filtration. -/
noncomputable def kerEquiv (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) :
    ↥((lvlCoeff V N).ker) ≃ₗ[ℝ] ↥(degStep V (N + 1)) where
  toFun x := ⟨(x : ↥(degStep V N)), by
    refine mem_degStep.mpr ⟨(x : ↥(degStep V N)).2.1, fun s hs => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with h | h
    · exact (x : ↥(degStep V N)).2.2 s h
    · have hs' : ofLex (toLex s) ∈ degLevel N := (mem_degLevel_iff.mpr h : ofLex (toLex s) ∈ degLevel N)
      have hker := congrFun (LinearMap.mem_ker.mp x.2) (⟨toLex s, hs'⟩ : lvlIx σ N)
      rw [lvlCoeff_apply, ofLex_toLex] at hker
      exact hker⟩
  invFun y := ⟨⟨(y : MvPowerSeries σ ℝ), degStep_antitone V (Nat.le_succ N) y.2⟩, by
    refine LinearMap.mem_ker.mpr (funext fun s => ?_)
    rw [lvlCoeff_apply]
    exact (mem_degStep.mp y.2).2 _ (by rw [mem_degLevel_iff.mp s.2]; omega)⟩
  left_inv := fun x => Subtype.ext (Subtype.ext rfl)
  right_inv := fun y => Subtype.ext rfl
  map_add' := fun x y => Subtype.ext (by simp)
  map_smul' := fun c x => Subtype.ext (by simp)

theorem finrank_degStep_eq (V : Submodule ℝ (MvPowerSeries σ ℝ)) [Module.Finite ℝ V] (N : ℕ) :
    Module.finrank ℝ ↥(degStep V N) =
      Module.finrank ℝ ↥((lvlCoeff V N).range) + Module.finrank ℝ ↥(degStep V (N + 1)) := by
  have := finite_degStep V N
  have h := LinearMap.finrank_range_add_finrank_ker (lvlCoeff V N)
  rw [LinearEquiv.finrank_eq (kerEquiv V N)] at h
  exact h.symm

/-- **The number of degree-`N` leading exponents is the drop of the degree filtration at
`N`.** -/
theorem card_jumpFinset_eq (V : Submodule ℝ (MvPowerSeries σ ℝ)) [Module.Finite ℝ V] (N : ℕ) :
    (jumpFinset V N).card =
      Module.finrank ℝ ↥(degStep V N) - Module.finrank ℝ ↥(degStep V (N + 1)) := by
  have h1 : (jumpFinset V N).card =
      (↑(jumpFinset V N) : Set (Lex (ℕ × Lex (σ →₀ ℕ)))).ncard :=
    (Set.ncard_coe_finset (jumpFinset V N)).symm
  have h2 : (↑(jumpFinset V N) : Set (Lex (ℕ × Lex (σ →₀ ℕ)))).ncard = (pivotSet V N).ncard :=
    ncard_jumpFinset_eq_pivotSet V N
  have h3 : (pivotSet V N).ncard = Module.finrank ℝ ↥((lvlCoeff V N).range) := by
    show (Set.ncard {i : lvlIx σ N | ∃ f ∈ (lvlCoeff V N).range, f i ≠ 0 ∧
      ∀ j, j < i → f j = 0}) = Module.finrank ℝ ↥((lvlCoeff V N).range)
    exact Commons.LinearAlgebra.pivot_ncard_eq_finrank ((lvlCoeff V N).range)
  have h4 := finrank_degStep_eq V N
  omega

/-! ## Telescoping and the counting theorem -/

/-- Telescoping the successive differences of an antitone sequence of naturals. -/
theorem sum_range_sub_antitone (D : ℕ → ℕ) (hD : Antitone D) (N : ℕ) :
    ∑ n ∈ Finset.range N, (D n - D (n + 1)) = D 0 - D N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : D N ≤ D 0 := hD (Nat.zero_le N)
    have h2 : D (N + 1) ≤ D N := hD (Nat.le_succ N)
    omega

/-- The set of leading-exponent keys of the elements of `V`. -/
def jumpSet (V : Submodule ℝ (MvPowerSeries σ ℝ)) : Set (Lex (ℕ × Lex (σ →₀ ℕ))) :=
  {key | ∃ f : MvPowerSeries σ ℝ, ∃ hf : f ≠ 0, f ∈ V ∧ leadExp f hf = key}

theorem jumpSet_eq_biUnion {V : Submodule ℝ (MvPowerSeries σ ℝ)} {Nmax : ℕ}
    (hN : degStep V Nmax = ⊥) :
    jumpSet V = ↑((Finset.range Nmax).biUnion (jumpFinset V)) := by
  ext key
  constructor
  · intro h
    obtain ⟨f, hf, hfV, hlead⟩ := h
    have hlt : minDeg f hf < Nmax := by
      by_contra hcon
      push Not at hcon
      have hmem : f ∈ degStep V Nmax :=
        (mem_degStep_iff_minDeg V hfV hf).mpr (by omega)
      rw [hN] at hmem
      exact hf (by simpa using hmem)
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨minDeg f hf, Finset.mem_range.mpr hlt, ?_⟩
    rw [← hlead, ← dk_udk_leadExp f hf]
    exact mem_jumpFinset_dk.mpr ⟨mem_degLevel_iff.mpr (tdeg_leadExp f hf), f, hf, hfV,
      (dk_udk_leadExp f hf).symm⟩
  · intro h
    rw [Finset.mem_coe, Finset.mem_biUnion] at h
    obtain ⟨N, -, hN'⟩ := h
    obtain ⟨s, -, ⟨f, hf, hfV, hlead⟩, hkey⟩ := mem_jumpFinset.mp hN'
    exact ⟨f, hf, hfV, hkey ▸ hlead⟩

/-- **The paper's Lemma `total jumps`**: the number of leading exponents of a finite-dimensional
subspace of `K⟦x₁,…,x_d⟧` equals its dimension. -/
theorem ncard_jumpSet_eq_finrank (V : Submodule ℝ (MvPowerSeries σ ℝ)) [Module.Finite ℝ V] :
    (jumpSet V).ncard = Module.finrank ℝ ↥V := by
  obtain ⟨Nmax, hNmax⟩ := exists_degStep_eq_bot V
  have hAnti : Antitone fun N => Module.finrank ℝ ↥(degStep V N) := by
    intro m n hmn
    have := finite_degStep V m
    exact Submodule.finrank_mono (degStep_antitone V hmn)
  have hpw : (↑(Finset.range Nmax) : Set ℕ).PairwiseDisjoint (jumpFinset V) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr fun key hka hkb => ?_
    obtain ⟨s₁, hs₁, -, hkey₁⟩ := mem_jumpFinset.mp hka
    obtain ⟨s₂, hs₂, -, hkey₂⟩ := mem_jumpFinset.mp hkb
    have hss : s₁ = s₂ := dk_injective (by rw [hkey₁, hkey₂])
    have : a = b := by rw [← mem_degLevel_iff.mp hs₁, hss, mem_degLevel_iff.mp hs₂]
    exact hab this
  calc (jumpSet V).ncard
      = (↑((Finset.range Nmax).biUnion (jumpFinset V)) :
          Set (Lex (ℕ × Lex (σ →₀ ℕ)))).ncard := by rw [jumpSet_eq_biUnion hNmax]
    _ = ((Finset.range Nmax).biUnion (jumpFinset V)).card := Set.ncard_coe_finset _
    _ = ∑ N ∈ Finset.range Nmax, (jumpFinset V N).card := Finset.card_biUnion hpw
    _ = ∑ N ∈ Finset.range Nmax,
          (Module.finrank ℝ ↥(degStep V N) - Module.finrank ℝ ↥(degStep V (N + 1))) :=
        Finset.sum_congr rfl fun N _ => card_jumpFinset_eq V N
    _ = Module.finrank ℝ ↥(degStep V 0) - Module.finrank ℝ ↥(degStep V Nmax) :=
        sum_range_sub_antitone _ hAnti Nmax
    _ = Module.finrank ℝ ↥V := by rw [degStep_zero, hNmax, finrank_bot, Nat.sub_zero]

end Submission.CDT.MvVanishing
