import Mathlib
import ChallengeDeps
import Submission.Work.BW.Defs
import Submission.Work.BW.DefsMult
import Submission.Work.BW.DefsMP
import Submission.Work.BW.zeroDeg_reduce
import Submission.Work.BW.applyW_cons_eq_applyDer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## The quotient (partial-degeneracy) reduction for `multiplicity_prop`

This file proves `quotient_reduction`: given a nonzero polynomial `P` whose degree in the
variable `Y_{i+1}` is `< 1` (i.e. `P` does not involve `Y_{i+1}`), and a vanishing condition
for the invariant derivatives `applyDer c t₀ t` at the points `ptS ℓ s`, we may drop the
coordinate `i` (on which `B` is nonzero), rename `P` on the remaining coordinates, and the
vanishing transports to `applyW`-derivatives at the points `ptTheta (exp ∘ ℓ ∘ σ) s`.

The mathematical heart is the linear-algebra fact `qr_span_w_top`: the vectors
`e₀` and `(0, c m ∘ σ)` span `ℂ^{N'+1}`. -/

/-- `e₀ ∘ liftIdx σ = e₀`: the only preimage of the coordinate `0` under `liftIdx σ` is `0`. -/
lemma qr_pi_single {N' r : ℕ} (σ : Fin N' → Fin r) :
    (Pi.single (0 : Fin (r+1)) (1:ℂ)) ∘ (liftIdx σ) = Pi.single (0 : Fin (N'+1)) (1:ℂ) := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · simp [Function.comp_apply, liftIdx, Fin.cases_zero]
  · simp [Function.comp_apply, liftIdx, Fin.cases_succ]

/-- `(0, c) ∘ liftIdx σ = (0, c ∘ σ)` for the invariant-derivation vectors. -/
lemma qr_cons {N' r : ℕ} (σ : Fin N' → Fin r) (c : Fin r → ℚ) :
    (Fin.cons 0 (fun i : Fin r => ((c i : ℚ):ℂ))) ∘ (liftIdx σ) =
      (Fin.cons 0 (fun j : Fin N' => ((c (σ j) : ℚ):ℂ))) := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩ <;>
    simp [Function.comp_apply, liftIdx, Fin.cases_zero, Fin.cases_succ]

/-- `ptTheta (exp ∘ ℓ) s = ptS ℓ s`. -/
lemma qr_ptS {r : ℕ} (ℓ : Fin r → ℂ) (s : ℕ) :
    ptTheta (fun j => Complex.exp (ℓ j)) s = ptS ℓ s := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · simp [ptTheta, ptS]
  · simp only [ptTheta, ptS, Fin.cons_succ]
    exact (Complex.exp_nat_mul (ℓ k) s).symm

/-- The rows `(c m (σ j))_j` span `ℚ^N` whenever `σ` is injective, avoids the coordinate `k`
with `B k ≠ 0`, and `B` generates the kernel of `c`. -/
lemma qr_rat_rows_span {N r : ℕ} (σ : Fin N → Fin r) (hσ : Function.Injective σ)
    (c : Fin (r-1) → Fin r → ℚ) (B : Fin r → ℤ)
    (hker : ∀ u : Fin r → ℚ, (∀ m, ∑ i, c m i * u i = 0) →
      ∃ t : ℚ, u = fun i => t * (B i : ℚ))
    (k : Fin r) (hk : k ∉ Set.range σ) (hBk : B k ≠ 0) :
    Submodule.span ℚ (Set.range (fun m : Fin (r-1) => (fun j : Fin N => c m (σ j)))) = ⊤ := by
  classical
  let M : Matrix (Fin (r-1)) (Fin N) ℚ := fun m j => c m (σ j)
  have hrow : M.row = (fun m : Fin (r-1) => (fun j : Fin N => c m (σ j))) := rfl
  have hmulvec : ∀ (v : Fin N → ℚ) (m : Fin (r-1)), (M.mulVec v) m = ∑ j, c m (σ j) * v j := by
    intro v m; rw [Matrix.mulVec_apply]; rfl
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv1 : M.mulVecLin v = 0 := LinearMap.mem_ker.mp hv
    have hv0 : M.mulVec v = 0 := by rwa [Matrix.mulVecLin_apply] at hv1
    have hu : ∀ m, ∑ i, c m i * (Function.extend σ v 0 : Fin r → ℚ) i = 0 := by
      intro m
      rw [zeroDeg_sum_range_eq σ hσ (fun i => c m i * (Function.extend σ v 0 : Fin r → ℚ) i)
            (fun i hi => by
              rw [Function.extend_apply' (f := σ) v (0 : Fin r → ℚ) i
                    (by simpa [Set.mem_range] using hi)]
              simp)]
      simp only [Function.Injective.extend_apply hσ v (0 : Fin r → ℚ)]
      rw [← hmulvec v m]
      exact congr_fun hv0 m
    obtain ⟨t, ht⟩ := hker _ hu
    have huk : (Function.extend σ v 0 : Fin r → ℚ) k = 0 := by
      rw [Function.extend_apply' (f := σ) v (0 : Fin r → ℚ) k (by simpa [Set.mem_range] using hk)]
      simp
    have hBk' : ((B k : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hBk
    have ht0 : t = 0 := by
      have h1 := congr_fun ht k
      rw [huk] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hBk'
    funext j
    have h2 := congr_fun ht (σ j)
    rw [Function.Injective.extend_apply hσ v (0 : Fin r → ℚ) j] at h2
    rw [ht0, zero_mul] at h2
    exact h2
  have hrank : M.rank = N := by
    rw [Matrix.rank]
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [LinearMap.ker_eq_bot.mpr hinj] at h
    rw [show Module.finrank ℚ ↥(⊥ : Submodule ℚ (Fin N → ℚ)) = 0 from finrank_bot ℚ _,
        add_zero, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact h
  rw [← hrow]
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank_eq_finrank_span_row M, hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The `w`-family `(e₀, (0, c m ∘ σ))` spans `ℂ^{N+1}`. -/
theorem qr_span_w_top {N r : ℕ} (σ : Fin N → Fin r) (hσ : Function.Injective σ)
    (c : Fin (r - 1) → Fin r → ℚ) (B : Fin r → ℤ)
    (hker : ∀ u : Fin r → ℚ, (∀ m, ∑ i, c m i * u i = 0) →
      ∃ t : ℚ, u = fun i => t * (B i : ℚ))
    (k : Fin r) (hk : k ∉ Set.range σ) (hBk : B k ≠ 0)
    (w : Fin (r - 1 + 1) → Fin (N + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (N + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun j : Fin N => ((c m (σ j) : ℚ) : ℂ))) :
    Submodule.span ℂ (Set.range w) = ⊤ := by
  classical
  set v : Fin (r-1) → Fin N → ℚ := fun m j => c m (σ j) with hv
  set vC : Fin (r-1) → Fin N → ℂ := fun m j => ((c m (σ j) : ℚ) : ℂ) with hvC
  have hrowtop : Submodule.span ℚ (Set.range v) = ⊤ := by
    rw [hv]; exact qr_rat_rows_span σ hσ c B hker k hk hBk
  have hbasis_span : Submodule.span ℂ (Set.range (fun j : Fin N => Pi.single j (1:ℂ))) = ⊤ := by
    have h : Set.range (fun j : Fin N => Pi.single j (1:ℂ)) = Set.range (Pi.basisFun ℂ (Fin N)) := by
      congr 1; funext j; exact (Pi.basisFun_apply ℂ (Fin N) j).symm
    rw [h, (Pi.basisFun ℂ (Fin N)).span_eq]
  have hbasis_sub : Set.range (fun j : Fin N => Pi.single j (1:ℂ))
      ⊆ Set.range (fun x : Fin N → ℚ => fun j => (x j : ℂ)) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j (1:ℚ), by funext j'; by_cases h : j' = j <;> simp [h]⟩
  have hcoe_span : Submodule.span ℂ (Set.range (fun x : Fin N → ℚ => fun j => (x j : ℂ))) = ⊤ :=
    le_antisymm le_top (by rw [← hbasis_span]; exact Submodule.span_mono hbasis_sub)
  have hcoe_le : Submodule.span ℂ (Set.range (fun x : Fin N → ℚ => fun j => (x j : ℂ)))
      ≤ Submodule.span ℂ (Set.range vC) := by
    apply Submodule.span_le.mpr
    rintro x ⟨ξ, rfl⟩
    change (fun j => (ξ j : ℂ)) ∈ Submodule.span ℂ (Set.range vC)
    have hmem : ξ ∈ Submodule.span ℚ (Set.range v) := by rw [hrowtop]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun m => ((a m : ℚ) : ℂ), ?_⟩
    funext j
    have hj : ∑ m, a m * (c m (σ j)) = ξ j := by
      have := congr_fun ha j
      simpa only [Finset.sum_apply, Pi.smul_apply, hv, smul_eq_mul] using this
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [hvC, ← hj]
    push_cast
    simp only [smul_eq_mul]
  have hCtop : Submodule.span ℂ (Set.range vC) = ⊤ :=
    le_antisymm le_top (by rw [← hcoe_span]; exact hcoe_le)
  have e0_mem : w 0 ∈ Submodule.span ℂ (Set.range w) := Submodule.subset_span ⟨0, rfl⟩
  have cons0_mem : ∀ γ : Fin N → ℂ, Fin.cons 0 γ ∈ Submodule.span ℂ (Set.range w) := by
    intro γ
    have hmem : γ ∈ Submodule.span ℂ (Set.range vC) := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    have hlin : Fin.cons 0 (∑ m : Fin (r-1), b m • vC m)
        = ∑ m : Fin (r-1), b m • (Fin.cons 0 (vC m)) := by
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
      · simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply, smul_zero, Finset.sum_const_zero]
      · simp only [Fin.cons_succ, Finset.sum_apply, Pi.smul_apply]
    have heq : Fin.cons 0 γ = ∑ m : Fin (r-1), b m • w m.succ := by
      rw [← hb, hlin]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hw1 m]
    rw [heq]
    exact Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m.succ, rfl⟩))
  rw [Submodule.eq_top_iff']
  intro δ
  have hdecomp : δ = (δ 0) • w 0 + Fin.cons 0 (Fin.tail δ) := by
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
    · simp [hw0, Fin.cons_zero, Pi.single_eq_same, smul_eq_mul]
    · simp only [hw0, Fin.cons_succ, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (Fin.succ_ne_zero l), smul_zero, zero_add]
      rfl
  rw [hdecomp]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ e0_mem) (cons0_mem (Fin.tail δ))

set_option maxHeartbeats 2000000 in
/-- **Quotient (partial-degeneracy) reduction.** If `P ≠ 0` has `deg_{Y_{i+1}} P < 1` and the
invariant derivatives of `P` vanish on the cyclic semigroup points `ptS ℓ s` up to the budgets
`𝒮, 𝒯`, then on the coordinates `Zᶜ` (where `Z = {j : 𝒟 j.succ < 1}`) `P` is the rename of a
nonzero polynomial `P'` in `N' + 1 ≤ r` variables, whose `applyW`-derivatives (with the
transported `w` and points `ptTheta (exp ∘ ℓ ∘ σ)`) vanish on the corresponding budgets. -/
theorem quotient_reduction {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (hP : P ≠ 0)
    (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j) (h𝒟0 : 1 ≤ 𝒟 0)
    (Sq Tq : ℕ → ℕ) (𝒮 𝒯 : ℝ)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (c : Fin (r - 1) → Fin r → ℚ) (B : Fin r → ℤ) (hB : B ≠ 0)
    (hker : ∀ u : Fin r → ℚ, (∀ m, ∑ i, c m i * u i = 0) →
      ∃ t : ℚ, u = fun i => t * (B i : ℚ))
    (ℓ : Fin r → ℂ)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0)
    (i : Fin r) (hi : 𝒟 i.succ < 1) (hBi : B i ≠ 0) :
    ∃ (N' : ℕ) (σ : Fin N' → Fin r) (P' : MvPolynomial (Fin (N' + 1)) ℂ) (δ : Fin (N' + 1) → ℝ)
      (w : Fin (r - 1 + 1) → Fin (N' + 1) → ℂ),
      N' < r ∧ Function.Injective σ ∧ i ∉ Set.range σ ∧ P' ≠ 0 ∧
      (∀ j, 0 ≤ δ j) ∧ 1 ≤ δ 0 ∧ (∀ j, 1 ≤ ⌊δ j⌋₊) ∧
      (∀ j, P'.degreeOf j ≤ ⌊δ j⌋₊) ∧
      Submodule.span ℂ (Set.range w) = ⊤ ∧
      (∀ j, δ j = 𝒟 (liftIdx σ j)) ∧
      (∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun j : Fin N' => ((c m (σ j) : ℚ) : ℂ))) ∧
      w 0 = Pi.single (0 : Fin (N' + 1)) (1 : ℂ) ∧
      (∀ s, s ≤ ∑ m ∈ Finset.range (N' + 1), Sq m → ∀ t : Fin (r - 1 + 1) → ℕ,
        ∑ k, t k ≤ ∑ m ∈ Finset.range (N' + 1), Tq m →
        MvPolynomial.eval (ptTheta (fun j => Complex.exp (ℓ (σ j))) s) (applyW w t P') = 0) := by
  classical
  have _hB : B ≠ 0 := hB
  -- `Z` is the set of coordinates where `𝒟 ≥ 1`; `σ` enumerates `Z` increasingly.
  set Z : Finset (Fin r) := Finset.univ.filter (fun k => 1 ≤ 𝒟 k.succ) with hZdef
  have hi_not_mem : i ∉ Z := by
    simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le.mpr hi
  set σ : Fin Z.card → Fin r := ⇑(Z.orderEmbOfFin rfl) with hσdef
  have hσmono : StrictMono σ := (Z.orderEmbOfFin rfl).strictMono
  have hσinj : Function.Injective σ := hσmono.injective
  have hσrange : Set.range σ = ↑Z := Finset.range_orderEmbOfFin Z rfl
  have hi_range : i ∉ Set.range σ := by rw [hσrange]; exact hi_not_mem
  have hσge : ∀ j, 1 ≤ 𝒟 (σ j).succ := by
    intro j
    have := Finset.orderEmbOfFin_mem Z rfl j
    simpa only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] using this
  have hσlt : ∀ k, k ∉ Set.range σ → 𝒟 k.succ < 1 := by
    intro k hk
    have hks : k ∉ Z := fun h => hk (by rw [hσrange]; exact h)
    simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] at hks
    exact not_le.mp hks
  have hN'lt : Z.card < r := by
    have hssub : Z ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ Z, fun h => hi_not_mem (h ▸ Finset.mem_univ i)⟩
    simpa using Finset.card_lt_card hssub
  have hZdeg : ∀ k, k ∉ Set.range σ → P.degreeOf k.succ = 0 := by
    intro k hk
    have hlt : (P.degreeOf k.succ : ℝ) < 1 := lt_of_le_of_lt (hdeg k.succ) (hσlt k hk)
    have : P.degreeOf k.succ < 1 := by exact_mod_cast hlt
    omega
  obtain ⟨P', hP'ren, hP'deg, hP'transfer⟩ :=
    zeroDeg_reduce (q := r - 1 + 1) σ hσmono P hZdeg
  -- the invariant-derivation family `W` on the big torus and the transported family `w`
  let W : Fin (r - 1 + 1) → Fin (r + 1) → ℂ :=
    Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun ii : Fin r => ((c m ii : ℚ) : ℂ)))
  let w : Fin (r - 1 + 1) → Fin (Z.card + 1) → ℂ :=
    Fin.cons (Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ)))
  have hWdef : W = Fin.cons (Pi.single (0 : Fin (r + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun ii : Fin r => ((c m ii : ℚ) : ℂ))) := rfl
  have hwdef : w = Fin.cons (Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ))
      (fun m : Fin (r - 1) => Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ))) := rfl
  have hWw : (fun k => W k ∘ liftIdx σ) = w := by
    rw [hWdef, hwdef]
    funext k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨m, rfl⟩
    · rw [Fin.cons_zero, Fin.cons_zero]; exact qr_pi_single σ
    · rw [Fin.cons_succ, Fin.cons_succ]; exact qr_cons σ (c m)
  have hw0 : w 0 = Pi.single (0 : Fin (Z.card + 1)) (1 : ℂ) := by
    rw [hwdef]; exact Fin.cons_zero _ _
  have hw1 : ∀ m : Fin (r - 1),
      w m.succ = Fin.cons 0 (fun j : Fin Z.card => ((c m (σ j) : ℚ) : ℂ)) := by
    intro m; rw [hwdef]; exact Fin.cons_succ _ _ _
  have hδnn : ∀ j : Fin (Z.card + 1), (0:ℝ) ≤ (fun j => 𝒟 (liftIdx σ j)) j := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp only [zeroDeg_liftIdx_zero]; linarith [h𝒟0]
    · simp only [zeroDeg_liftIdx_succ]; linarith [hσge k]
  have hδ0 : (1:ℝ) ≤ (fun j => 𝒟 (liftIdx σ j)) 0 := by
    simp only [zeroDeg_liftIdx_zero]; exact h𝒟0
  have hδ1 : ∀ j : Fin (Z.card + 1), (1:ℕ) ≤ ⌊(fun j => 𝒟 (liftIdx σ j)) j⌋₊ := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp only [zeroDeg_liftIdx_zero]; exact (Nat.one_le_floor_iff _).mpr h𝒟0
    · simp only [zeroDeg_liftIdx_succ]; exact (Nat.one_le_floor_iff _).mpr (hσge k)
  have hdeg' : ∀ j : Fin (Z.card + 1), P'.degreeOf j ≤ ⌊(fun j => 𝒟 (liftIdx σ j)) j⌋₊ := by
    intro j
    rw [hP'deg j]
    exact Nat.le_floor (by simpa using hdeg (liftIdx σ j))
  refine ⟨Z.card, σ, P', (fun j => 𝒟 (liftIdx σ j)), w,
    hN'lt, hσinj, hi_range, ?_, hδnn, hδ0, hδ1, hdeg', ?_, ?_, hw1, hw0, ?_⟩
  · intro h0; exact hP (by rw [← hP'ren, h0, map_zero])
  · rw [hwdef]
    exact qr_span_w_top σ hσinj c B hker i hi_range hBi w hw0 hw1
  · intro j; rfl
  · intro s hs t ht
    have hsub : Finset.range (Z.card + 1) ⊆ Finset.range (r + 1) := Finset.range_mono (by omega)
    have hSbound : (s : ℝ) ≤ 𝒮 := by
      have hle : (∑ m ∈ Finset.range (Z.card + 1), Sq m) ≤ (∑ m ∈ Finset.range (r + 1), Sq m) :=
        Finset.sum_le_sum_of_subset hsub
      have h1 : (s : ℝ) ≤ ((∑ m ∈ Finset.range (Z.card + 1), Sq m : ℕ) : ℝ) := by
        exact_mod_cast hs
      have h2 : ((∑ m ∈ Finset.range (Z.card + 1), Sq m : ℕ) : ℝ) ≤
          ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) := by exact_mod_cast hle
      linarith [h1, h2, hSsum]
    have hTbound : ((t 0 + ∑ m : Fin (r - 1), t m.succ : ℕ) : ℝ) ≤ 𝒯 := by
      have hle : (∑ m ∈ Finset.range (Z.card + 1), Tq m) ≤ (∑ m ∈ Finset.range (r + 1), Tq m) :=
        Finset.sum_le_sum_of_subset hsub
      have ht' : (t 0 + ∑ m : Fin (r - 1), t m.succ) ≤ ∑ m ∈ Finset.range (Z.card + 1), Tq m := by
        simpa only [Fin.sum_univ_succ] using ht
      have h1 : ((t 0 + ∑ m : Fin (r - 1), t m.succ : ℕ) : ℝ) ≤
          ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) := by
        exact_mod_cast le_trans ht' hle
      linarith [h1, hTsum]
    have hT := hP'transfer W t (fun j => Complex.exp (ℓ j)) s
    have hθσ : (fun j => Complex.exp (ℓ j)) ∘ σ = (fun j => Complex.exp (ℓ (σ j))) := by
      funext j; rfl
    rw [hWdef, hWw, hθσ, qr_ptS, applyW_cons_eq_applyDer] at hT
    exact hT.symm.trans (hvan s hSbound (t 0) (fun m => t m.succ) hTbound)

end Work.BW
