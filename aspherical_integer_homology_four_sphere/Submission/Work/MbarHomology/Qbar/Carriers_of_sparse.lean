import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped BigOperators

/-!
# The sparse criterion for face completeness

`PolytopeData` stores, for every face `f` and every constraint `i`, a decidable emptiness flag
`empSel f i` together with certificates of one of two kinds: Farkas infeasibility
certificates (`OkEmp`) for the region `Fset f ∩ {n_i = b_i}` when `empSel f i = true`, and
certificates that a face `addF f i` realises `tight f ∪ {i}` when `empSel f i = false` (`OkAdd`).
For the polytope `Q̄` of the aspherical homology 4-sphere the *shape* of these certificates is
different from the one hard-wired in `PolytopeData` (they are Farkas certificates produced by an
LP solver, as combinations of at most two constraints with a nonnegative side of at most three
terms), so the "sparse" data below is passed in as explicit arguments instead.

`Carriers_of_sparse` is the resulting criterion: `OkBasic` (only the face bookkeeping and the
positivity of the common denominator are needed) plus

* `hemp`: for every pair with `empSel f i = true`, a nonnegative combination
  `∑_t λ_t n_{idx_t}` of normals whose difference from `∑_k μ_k n_k + μ_I n_i` vanishes and whose
  right hand side is strictly smaller; and
* `hadd`: for every pair with `empSel f i = false`, a face `empAdd f i` whose tight set is *exactly*
  `tight f ∪ {i}`,

implies `P.Carriers`.

The proof is the same maximality argument as in `Carriers_of_Ok`: starting from a face of maximal
dimension whose tight set is contained in the carrier `tightAt x` of a point `x ∈ Pset`, a missing
constraint `i` cannot be certifiably empty (`hemp` would be violated at `x`), hence `hadd` produces a
strictly larger face inside the carrier, a contradiction.
-/

namespace Work.ConvexCells

/-- Real form of an integral linear combination of normals.  The `toE`-image of the integral
combination `∑_{k ∈ s} M k • nrm k + MI • nrm i - ∑_t c t • nrm (idx t)` is `D` times the same
combination of the real normals `nR`. -/
theorem sparse_toE_comb {d : ℕ} (P : PolytopeData d) (hD : 0 < P.D) {ι : Type*} [Fintype ι]
    (s : Finset (Fin P.m)) (i : Fin P.m) (M : Fin P.m → ℤ) (MI : ℤ)
    (c : ι → ℤ) (idx : ι → Fin P.m) :
    toE ((∑ k ∈ s, M k • P.nrm k) + MI • P.nrm i - ∑ t, c t • P.nrm (idx t))
      = (P.D : ℝ) • ((∑ k ∈ s, (M k : ℝ) • P.nR k) + (MI : ℝ) • P.nR i
          - ∑ t, (c t : ℝ) • P.nR (idx t)) := by
  have hDne : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD)
  have htr : ∀ t : Fin P.m, toE (P.nrm t) = (P.D : ℝ) • P.nR t := by
    intro t
    rw [PolytopeData.nR, smul_smul, mul_inv_cancel₀ hDne, one_smul]
  rw [toE_sub, toE_add, toE_sum s, toE_sum (Finset.univ)]
  simp only [toE_smul, htr]
  rw [smul_sub, smul_add, Finset.smul_sum, Finset.smul_sum]
  simp only [smul_smul, mul_comm]

/-- A Farkas infeasibility certificate in the sparse shape rules out a point of the polytope: if
`∑_k M k • n_k + MI • n_i = ∑_t c t • n_{idx t}` with `c ≥ 0` and the corresponding right hand side
is strictly positive, then no `x ∈ Pset` can be tight at all the `k ∈ s` and at `i`. -/
theorem sparse_emp_contra {d : ℕ} (P : PolytopeData d) (hD : 0 < P.D) {x : E d}
    (hx : x ∈ P.Pset) (s : Finset (Fin P.m)) (i : Fin P.m)
    (M : Fin P.m → ℤ) (MI : ℤ) (c : Fin 3 → ℤ) (idx : Fin 3 → Fin P.m)
    (hc : ∀ t, 0 ≤ c t)
    (hvec : ∀ j', (∑ k ∈ s, M k * P.nrm k j') + MI * P.nrm i j'
        = ∑ t : Fin 3, c t * P.nrm (idx t) j')
    (hf : ∀ k ∈ s, inner ℝ (P.nR k) x = P.bR k)
    (hi : inner ℝ (P.nR i) x = P.bR i)
    (hpos : 0 < (∑ k ∈ s, M k * P.rhs k) + MI * P.rhs i - ∑ t : Fin 3, c t * P.rhs (idx t)) :
    False := by
  have hDpos : (0:ℝ) < (P.D:ℝ) := by exact_mod_cast hD
  have hDne : (P.D : ℝ) ≠ 0 := ne_of_gt hDpos
  -- the integral vector identity
  have hvec0 : ((∑ k ∈ s, M k • P.nrm k) + MI • P.nrm i
      - ∑ t, c t • P.nrm (idx t) : Fin d → ℤ) = 0 := by
    funext j'
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    have h := hvec j'
    linarith
  -- its real form
  have hreal : (∑ k ∈ s, (M k : ℝ) • P.nR k) + (MI : ℝ) • P.nR i
      - ∑ t, (c t : ℝ) • P.nR (idx t) = 0 := by
    have h0 : toE ((∑ k ∈ s, M k • P.nrm k) + MI • P.nrm i - ∑ t, c t • P.nrm (idx t)) = 0 := by
      rw [hvec0, toE_zero]
    rw [sparse_toE_comb P hD s i M MI c idx] at h0
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hDne
    · exact h1
  -- the scalar identity
  have hscal : ∑ k ∈ s, (M k : ℝ) * inner ℝ (P.nR k) x + (MI : ℝ) * inner ℝ (P.nR i) x
      - ∑ t, (c t : ℝ) * inner ℝ (P.nR (idx t)) x = 0 := by
    have hthis := congrArg (fun v : E d => inner ℝ v x) hreal
    rw [inner_zero_left, inner_sub_left, inner_add_left] at hthis
    rw [PolytopeData.inner_lincomb_left s (fun k => (M k : ℝ)) (fun k : Fin P.m => P.nR k) x,
      PolytopeData.inner_lincomb_left Finset.univ (fun t : Fin 3 => (c t : ℝ))
        (fun t : Fin 3 => P.nR (idx t)) x] at hthis
    simp only [inner_smul_left, RCLike.conj_to_real] at hthis
    exact hthis
  -- the inequality coming from `x ∈ Pset`
  have hle : ∑ k ∈ s, (M k : ℝ) * P.bR k + (MI : ℝ) * P.bR i
      - ∑ t : Fin 3, (c t : ℝ) * P.bR (idx t) ≤ 0 := by
    have hsum_le : ∑ t : Fin 3, (c t : ℝ) * inner ℝ (P.nR (idx t)) x
        ≤ ∑ t : Fin 3, (c t : ℝ) * P.bR (idx t) :=
      Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (hx (idx t)) (by exact_mod_cast hc t)
    have hXeq : ∑ k ∈ s, (M k : ℝ) * inner ℝ (P.nR k) x = ∑ k ∈ s, (M k : ℝ) * P.bR k :=
      Finset.sum_congr rfl fun k hk => by rw [hf k hk]
    have hIeq : (MI : ℝ) * inner ℝ (P.nR i) x = (MI : ℝ) * P.bR i := by rw [hi]
    linarith [hscal, hsum_le, hXeq, hIeq]
  -- ... and the strict inequality of the certificate
  have hposR : 0 < ∑ k ∈ s, (M k : ℝ) * P.bR k + (MI : ℝ) * P.bR i
      - ∑ t : Fin 3, (c t : ℝ) * P.bR (idx t) := by
    have h1 : (0:ℝ) < (((∑ k ∈ s, M k * P.rhs k) + MI * P.rhs i
        - ∑ t : Fin 3, c t * P.rhs (idx t) : ℤ) : ℝ) := by exact_mod_cast hpos
    have hsumA : ∑ k ∈ s, (M k : ℝ) * P.bR k
        = (∑ k ∈ s, (M k : ℝ) * (P.rhs k : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hsumG : ∑ t : Fin 3, (c t : ℝ) * P.bR (idx t)
        = (∑ t : Fin 3, (c t : ℝ) * (P.rhs (idx t) : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun t _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hI : (MI : ℝ) * P.bR i = (MI : ℝ) * (P.rhs i : ℝ) / (P.D : ℝ) := by
      rw [PolytopeData.bR, mul_div_assoc]
    have hcast : (((∑ k ∈ s, M k * P.rhs k) + MI * P.rhs i
        - ∑ t : Fin 3, c t * P.rhs (idx t) : ℤ) : ℝ)
        = ((∑ k ∈ s, (M k : ℝ) * P.bR k) + (MI : ℝ) * P.bR i
            - ∑ t : Fin 3, (c t : ℝ) * P.bR (idx t)) * (P.D : ℝ) := by
      rw [hsumA, hsumG, hI, ← add_div, ← sub_div, div_mul_cancel₀ _ hDne]
      push_cast
      ring
    rw [hcast] at h1
    nlinarith [h1, hDpos]
  linarith

end Work.ConvexCells

namespace Work.MbarHomology.Qbar

open Work.ConvexCells

/-- **Face completeness from sparse certificates.**  If the decidable emptiness flags come with
Farkas infeasibility certificates for the empty regions (`hemp`) and with faces realising
`tight f ∪ {i}` exactly for the nonempty ones (`hadd`), then every point of the polytope has its
tight set among the listed faces. -/
theorem Carriers_of_sparse {d : ℕ} (P : Work.ConvexCells.PolytopeData d) (h : P.OkBasic)
    (empSel : Fin P.K → Fin P.m → Bool)
    (empMu : Fin P.K → Fin P.m → Fin P.m → ℤ)
    (empMuI : Fin P.K → Fin P.m → ℤ)
    (empLamIdx : Fin P.K → Fin P.m → Fin 3 → Fin P.m)
    (empLamVal : Fin P.K → Fin P.m → Fin 3 → ℤ)
    (empAdd : Fin P.K → Fin P.m → Fin P.K)
    (hemp : ∀ (f : Fin P.K) (i : Fin P.m), empSel f i = true →
      (∀ t : Fin 3, 0 ≤ empLamVal f i t) ∧
      (∀ j' : Fin d, (∑ k ∈ P.tight f, empMu f i k * P.nrm k j') + empMuI f i * P.nrm i j'
          = ∑ t : Fin 3, empLamVal f i t * P.nrm (empLamIdx f i t) j') ∧
      (0 < (∑ k ∈ P.tight f, empMu f i k * P.rhs k) + empMuI f i * P.rhs i
          - ∑ t : Fin 3, empLamVal f i t * P.rhs (empLamIdx f i t)))
    (hadd : ∀ (f : Fin P.K) (i : Fin P.m), empSel f i = false → P.tight (empAdd f i) = P.tight f ∪ {i}) :
    P.Carriers := by
  classical
  have hD : 0 < P.D := h.1
  have htop : P.tight P.top = ∅ := h.2.1
  intro x hx
  -- membership in `tightAt x` is equality at `x`, for points of the polytope
  have hTAt : ∀ k : Fin P.m, k ∈ P.tightAt x ↔ inner ℝ (P.nR k) x = P.bR k :=
    fun k => PolytopeData.tightAt_of_mem P hx k
  -- a face whose tight set is a proper subset of the carrier can be enlarged inside the carrier
  have key : ∀ f : Fin P.K, P.tight f ⊆ P.tightAt x → P.tight f ≠ P.tightAt x →
      ∃ g : Fin P.K, P.tight f ⊂ P.tight g ∧ P.tight g ⊆ P.tightAt x := by
    intro f hf hne
    have hssub : P.tight f ⊂ P.tightAt x := Finset.ssubset_iff_subset_ne.mpr ⟨hf, hne⟩
    obtain ⟨i, hiA, hi_not⟩ := Finset.exists_of_ssubset hssub
    have hlin : ∀ k ∈ P.tight f, inner ℝ (P.nR k) x = P.bR k :=
      fun k hk => (hTAt k).mp (hf hk)
    have hii : inner ℝ (P.nR i) x = P.bR i := (hTAt i).mp hiA
    have hsel : empSel f i = false := by
      cases hb : empSel f i with
      | false => rfl
      | true =>
        obtain ⟨hc, hvec, hpos⟩ := hemp f i hb
        exact (sparse_emp_contra P hD hx (P.tight f) i (empMu f i)
          (empMuI f i) (empLamVal f i) (empLamIdx f i) hc hvec hlin hii hpos).elim
    refine ⟨empAdd f i, ?_, ?_⟩
    · rw [hadd f i hsel]
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
      intro hcontra
      have hmem : i ∈ P.tight f := by
        rw [hcontra]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self i)
      exact hi_not hmem
    · rw [hadd f i hsel]
      intro k hk
      rw [hTAt k]
      rw [Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact hlin k hk
      · rw [Finset.mem_singleton.mp hk]
        exact hii
  -- a face of maximal cardinality among those whose tight set lies in the carrier
  obtain ⟨f, hfS, hfmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun f : Fin P.K => P.tight f ⊆ P.tightAt x)
    (fun f => (P.tight f).card)
    ⟨P.top, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [htop]
      exact Finset.empty_subset _⟩
  have hf : P.tight f ⊆ P.tightAt x := (Finset.mem_filter.mp hfS).2
  refine ⟨f, ?_⟩
  by_contra hne
  obtain ⟨g, hgsub, hgsub2⟩ := key f hf hne
  have hgS : g ∈ Finset.univ.filter (fun f : Fin P.K => P.tight f ⊆ P.tightAt x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hgsub2⟩
  have hlt : (P.tight f).card < (P.tight g).card := Finset.card_lt_card hgsub
  have hle := hfmax g hgS
  omega

end Work.MbarHomology.Qbar
