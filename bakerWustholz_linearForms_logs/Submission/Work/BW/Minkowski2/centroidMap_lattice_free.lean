import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.lam_castSucc_le_succ
import Submission.Work.BW.Minkowski2.half_sub_mem_interior

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The centroid map is injective modulo the lattice

For a lattice `Λ ⊆ ℝᵈ`, a symmetric convex body `K` with `p, q ∈ interior K`, and `λ` satisfying
the flag hypotheses of Minkowski's second theorem, the "centroid combination"

`∑ᵢ ((λ_{i+1} - λ_i)/2) • c i p - ∑ᵢ ((λ_{i+1} - λ_i)/2) • c i q`

of two interior points `p ≠ q` is never a lattice vector.  This is the injectivity-modulo-`Λ`
step in the section-map (Davenport/Estermann) proof of Minkowski's second theorem.

The argument: let `k` be the largest index with `p k ≠ q k`.  Since `c i` depends only on the
coordinates `≥ i`, the vectors `c i p` and `c i q` coincide for `i > k`, so the combination
only involves `i ≤ k`.  Writing `α i = (λ_{i+1} - λ_i)/2 ≥ 0` and `w i = c i p - c i q`, all the
`w i / 2` lie in `interior K`, and `∑_{i ≤ k} α i = λ_{k+1}/2` by telescoping.  Hence the
combination lies in `λ_{k+1} • interior K = interior (λ_{k+1} • K)`, while its `k`-th coordinate
equals `(λ_{k+1}/2) * (p k - q k) ≠ 0`, contradicting the flag hypothesis at `k`.
-/

open scoped Pointwise

namespace Work.BW.Minkowski2

/-- Telescoping: the increments `lam i.succ - lam i.castSucc` over the initial segment
`{i : Fin d | i ≤ k}` sum to `lam k.succ - lam 0`. -/
lemma sum_incr_filter {d : ℕ} (lam : Fin (d+1) → ℝ) (k : Fin d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), (lam i.succ - lam i.castSucc))
      = lam k.succ - lam 0 := by
  have main : ∀ n : ℕ, ∀ k : Fin d, k.val = n →
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), (lam i.succ - lam i.castSucc))
        = lam k.succ - lam 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hf : Finset.univ.filter (fun i : Fin d => i ≤ k) = {k} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          rw [Fin.le_def] at h
          omega
        · intro h
          subst h
          exact le_rfl
      rw [hf, Finset.sum_singleton]
      have hcs : (k.castSucc : Fin (d+1)) = 0 := by
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using hk
      rw [hcs]
    | succ n ih =>
      intro k hk
      have hnd : n < d := by omega
      have hkn : k.val = n + 1 := by omega
      have hsub : ∀ (i : Fin d), i ≤ k ↔ i = k ∨ i ≤ (⟨n, hnd⟩ : Fin d) := by
        intro i
        constructor
        · intro hi
          rw [Fin.le_def] at hi
          by_cases h : i = k
          · exact Or.inl h
          · refine Or.inr ?_
            rw [Fin.le_def]
            simp only [Fin.val_mk]
            have hne : i.val ≠ k.val := by
              intro hc
              exact h (Fin.ext hc)
            omega
        · rintro (rfl | hi)
          · exact le_rfl
          · rw [Fin.le_def] at hi ⊢
            simp only [Fin.val_mk] at hi
            omega
      have hfil : Finset.univ.filter (fun i : Fin d => i ≤ k)
          = insert k (Finset.univ.filter (fun i : Fin d => i ≤ (⟨n, hnd⟩ : Fin d))) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        exact hsub i
      have hnk : k ∉ Finset.univ.filter (fun i : Fin d => i ≤ (⟨n, hnd⟩ : Fin d)) := by
        rw [Finset.mem_filter]
        rintro ⟨-, hle⟩
        rw [Fin.le_def] at hle
        simp only [Fin.val_mk] at hle
        omega
      rw [hfil, Finset.sum_insert hnk]
      rw [ih (⟨n, hnd⟩ : Fin d) rfl]
      have hcs : (k.castSucc : Fin (d+1)) = (⟨n, hnd⟩ : Fin d).succ := by
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk] using hkn
      rw [hcs]
      ring
  exact main k.val k rfl

theorem centroidMap_lattice_free {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ))
    (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0) (hpos : ∀ i : Fin d, 0 < lam i.succ)
    (hmono : ∀ i j : Fin d, i ≤ j → lam i.succ ≤ lam j.succ)
    (hflag : ∀ (i : Fin d) (z : Fin d → ℝ), z ∈ (Λ : Set (Fin d → ℝ)) →
      z ∈ interior (Work.BW.smulSet (lam i.succ) K) → ∀ m : Fin d, i ≤ m → z m = 0)
    (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ))
    (hcint : ∀ (i : Fin d) (x : Fin d → ℝ), x ∈ interior K → c i x ∈ interior K)
    (hcfix : ∀ (i : Fin d) (x : Fin d → ℝ) (m : Fin d), i ≤ m → c i x m = x m)
    (hcdep : ∀ (i : Fin d) (x y : Fin d → ℝ), (∀ m, i ≤ m → x m = y m) → c i x = c i y)
    {p q : Fin d → ℝ} (hp : p ∈ interior K) (hq : q ∈ interior K) (hpq : p ≠ q) :
    ∀ z ∈ (Λ : Set (Fin d → ℝ)),
      (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i p)
        - (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i q) ≠ z := by
  have hincr : ∀ (k : Fin d),
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), (lam i.succ - lam i.castSucc))
        = lam k.succ - lam 0 := fun k => sum_incr_filter lam k
  have hlam_mono : ∀ (i : Fin d), lam i.castSucc ≤ lam i.succ :=
    fun i => lam_castSucc_le_succ lam hlam0 hpos hmono i
  have hhalf : ∀ {u v : Fin d → ℝ}, u ∈ interior K → v ∈ interior K →
      (1/2 : ℝ) • (u - v) ∈ interior K := fun hu hv => half_sub_mem_interior hKc hsym hu hv
  intro z hz hzeq
  set α : Fin d → ℝ := fun i => (lam i.succ - lam i.castSucc) / 2 with hαdef
  have hα_def : ∀ i : Fin d, α i = (lam i.succ - lam i.castSucc) / 2 := fun i => by
    simp only [hαdef]
  have hα_nonneg : ∀ i : Fin d, 0 ≤ α i := by
    intro i
    rw [hα_def i]
    exact div_nonneg (by linarith [hlam_mono i]) (by norm_num)
  obtain ⟨k, hkne, hkmax⟩ : ∃ k : Fin d, p k ≠ q k ∧ ∀ m : Fin d, k < m → p m = q m := by
    have hex : ∃ m : Fin d, p m ≠ q m := by
      by_contra h
      exact hpq (funext fun m => by by_contra hm; exact h ⟨m, hm⟩)
    let T : Finset (Fin d) := Finset.univ.filter (fun m : Fin d => p m ≠ q m)
    have hTne : T.Nonempty := by
      obtain ⟨m, hm⟩ := hex
      exact ⟨m, by simp [T, hm]⟩
    refine ⟨T.max' hTne, ?_, ?_⟩
    · have hmem := Finset.max'_mem T hTne
      simpa [T] using hmem
    · intro m hm
      by_contra hne
      have hle : m ≤ T.max' hTne := Finset.le_max' T m (by simp [T, hne])
      exact absurd hle (not_le.mpr hm)
  have hw : ∀ i : Fin d, k < i → c i p - c i q = 0 := by
    intro i hi
    have hdep : ∀ m : Fin d, i ≤ m → p m = q m := fun m him => hkmax m (lt_of_lt_of_le hi him)
    rw [hcdep i p q hdep, sub_self]
  have hzeqα : (∑ i : Fin d, α i • c i p) - (∑ i : Fin d, α i • c i q) = z := by
    simpa only [hαdef] using hzeq
  have hsum1 : (∑ i : Fin d, α i • (c i p - c i q)) = z := by
    have h2 : (∑ i : Fin d, α i • (c i p - c i q))
        = (∑ i : Fin d, α i • c i p) - (∑ i : Fin d, α i • c i q) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
    rw [h2, hzeqα]
  have hSz : (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), α i • (c i p - c i q)) = z := by
    rw [← hsum1]
    refine Finset.sum_subset (fun i _ => Finset.mem_univ i) ?_
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hw i (lt_of_not_ge hi), smul_zero]
  have hcoord : ∀ m : Fin d, k ≤ m → z m =
      (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), α i) * (p m - q m) := by
    intro m hm
    rw [← hSz]
    rw [Finset.sum_apply]
    have hfix : ∀ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k),
        (α i • (c i p - c i q)) m = α i * (p m - q m) := by
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hcfix i p m (le_trans hik hm),
        hcfix i q m (le_trans hik hm)]
    trans (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), α i * (p m - q m))
    · exact Finset.sum_congr rfl hfix
    · exact (Finset.sum_mul _ _ _).symm
  have hαsum : (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), α i)
      = lam k.succ / 2 := by
    rw [show (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k), α i)
        = (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k),
            (lam i.succ - lam i.castSucc) / 2) from
      Finset.sum_congr rfl fun i _ => hα_def i]
    rw [← Finset.sum_div, hincr k, hlam0, sub_zero]
  have hzk : z k ≠ 0 := by
    rw [hcoord k le_rfl, hαsum]
    have hl_ne : (0:ℝ) < lam k.succ / 2 := by linarith [hpos k]
    exact mul_ne_zero (ne_of_gt hl_ne) (sub_ne_zero.mpr hkne)
  set Y : Fin d → ℝ := ∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k),
      (2 * α i / lam k.succ) • ((1/2 : ℝ) • (c i p - c i q)) with hY
  have hy : Y ∈ interior K := by
    rw [hY]
    refine (hKc.interior).sum_mem ?_ ?_ ?_
    · intro i _
      exact div_nonneg (by linarith [hα_nonneg i]) (le_of_lt (hpos k))
    · rw [← Finset.sum_div, ← Finset.mul_sum, hαsum]
      have hl_ne : lam k.succ ≠ 0 := ne_of_gt (hpos k)
      rw [show 2 * (lam k.succ / 2) = lam k.succ by ring, div_self hl_ne]
    · intro i _
      exact hhalf (hcint i p hp) (hcint i q hq)
  have hsy : lam k.succ • Y = ∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ k),
      α i • (c i p - c i q) := by
    rw [hY]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← mul_assoc, mul_div_cancel₀ (2 * α i) (ne_of_gt (hpos k))]
      ring
  have hzint : z ∈ interior (Work.BW.smulSet (lam k.succ) K) := by
    rw [Work.BW.smulSet_eq, interior_smul₀ (ne_of_gt (hpos k)) K, ← hSz, ← hsy]
    exact Set.smul_mem_smul_set hy
  exact hzk (hflag k z hz hzint k le_rfl)

end Work.BW.Minkowski2
