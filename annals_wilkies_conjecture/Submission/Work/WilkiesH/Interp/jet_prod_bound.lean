import Mathlib

set_option linter.unusedVariables false

open scoped Topology

namespace Work.WilkiesH.Interp

/-- Auxiliary lemma: norm bound for the `n`-th iterated derivative of a product of `d` functions,
stated `Within` a set `s` on which all the factors are `C^j`.

The hypotheses are those of `jet_prod_bound`, with `iteratedFDerivWithin` in place of
`iteratedFDeriv`, and the conclusion holds at *every* order `n ≤ j` — which is what makes the
induction on the number of factors go through, since the Leibniz (bilinear) estimate for the
`n`-th derivative of a product involves the derivatives of the sub-product at all lower orders. -/
theorem norm_prod_le_within : ∀ (d : ℕ) (m j : ℕ) (s : Set (Fin m → ℝ))
    (f : Fin d → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hdiff : ∀ i, ContDiffOn ℝ (j : ℕ) (f i) s)
    (hval : ∀ i, ‖f i x‖ ≤ 1)
    (hjet : ∀ i, ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ 1),
    ∀ n, n ≤ j → ‖iteratedFDerivWithin ℝ n (fun y => ∏ i, f i y) s x‖ ≤ (d : ℝ) ^ n := by
  intro d
  induction d with
  | zero =>
    intro m j s f x hs hx hdiff hval hjet n hn
    have h1 : (fun y : Fin m → ℝ => ∏ i : Fin 0, f i y) = fun _ => (1 : ℝ) := by
      funext y; simp
    rw [h1]
    rcases n with _ | k
    · rw [norm_iteratedFDerivWithin_zero]; simp
    · rw [iteratedFDerivWithin_succ_const]; simp
  | succ d IH =>
    intro m j s f x hs hx hdiff hval hjet n hn
    let g : (Fin m → ℝ) → ℝ := fun y => ∏ i : Fin d, f i.castSucc y
    let hh : (Fin m → ℝ) → ℝ := f (Fin.last d)
    have hprod : (fun y : Fin m → ℝ => ∏ i : Fin (d + 1), f i y) = fun y => g y * hh y := by
      funext y
      simp only [g, hh]
      exact Fin.prod_univ_castSucc (fun i : Fin (d + 1) => f i y)
    rw [hprod]
    have hg_diff : ContDiffOn ℝ (j : ℕ) g s := by
      simp only [g]
      exact contDiffOn_prod (fun i _ => hdiff i.castSucc)
    have hh_diff : ContDiffOn ℝ (j : ℕ) hh s := by
      simp only [hh]
      exact hdiff (Fin.last d)
    have IHsub : ∀ k, k ≤ j → ‖iteratedFDerivWithin ℝ k g s x‖ ≤ (d : ℝ) ^ k := by
      intro k hk
      have key := IH m j s (fun i : Fin d => f i.castSucc) x hs hx
        (fun i => hdiff i.castSucc) (fun i => hval i.castSucc)
        (fun i k' hk1 hk2 => hjet i.castSucc k' hk1 hk2) k hk
      simpa only [g] using key
    have hmul := norm_iteratedFDerivWithin_mul_le (f := g) (g := hh) (s := s)
      (N := (j : WithTop ℕ∞)) (n := n) hg_diff hh_diff hs hx (by exact_mod_cast hn)
    calc ‖iteratedFDerivWithin ℝ n (fun y => g y * hh y) s x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i g s x‖
            * ‖iteratedFDerivWithin ℝ (n - i) hh s x‖ := hmul
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (d : ℝ) ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hgi : ‖iteratedFDerivWithin ℝ i g s x‖ ≤ (d : ℝ) ^ i :=
            IHsub i (le_trans hi_le hn)
          have hhi : ‖iteratedFDerivWithin ℝ (n - i) hh s x‖ ≤ 1 := by
            rcases Nat.eq_zero_or_pos (n - i) with h0 | hpos
            · rw [h0, norm_iteratedFDerivWithin_zero]
              simpa only [hh] using hval (Fin.last d)
            · simpa only [hh] using
                hjet (Fin.last d) (n - i) hpos (le_trans (Nat.sub_le n i) hn)
          have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := by positivity
          have hdi : (0 : ℝ) ≤ (d : ℝ) ^ i := by positivity
          calc (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i g s x‖
                * ‖iteratedFDerivWithin ℝ (n - i) hh s x‖
              ≤ (n.choose i : ℝ) * (d : ℝ) ^ i
                * ‖iteratedFDerivWithin ℝ (n - i) hh s x‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgi hc) (norm_nonneg _)
            _ ≤ (n.choose i : ℝ) * (d : ℝ) ^ i * 1 :=
                mul_le_mul_of_nonneg_left hhi (mul_nonneg hc hdi)
            _ = (n.choose i : ℝ) * (d : ℝ) ^ i := mul_one _
      _ = ((d : ℝ) + 1) ^ n := by
          rw [add_pow]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [one_pow, mul_one]
          ring
      _ = ((d + 1 : ℕ) : ℝ) ^ n := by
          rw [Nat.cast_add, Nat.cast_one]

/-- Norm bound for the `j`-th iterated derivative of a product of `d` functions. -/
theorem norm_prod_le {m d j : ℕ} (f : Fin d → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (hdiff : ∀ i, ContDiffAt ℝ (j : ℕ) (f i) x)
    (hval : ∀ i, |f i x| ≤ 1)
    (hjet : ∀ i, ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x‖ ≤ (d : ℝ) ^ j := by
  -- Each factor is `C^j` on some open neighbourhood of `x`; intersect finitely many of them.
  have hstep : ∀ i : Fin d,
      ∃ u : Set (Fin m → ℝ), IsOpen u ∧ x ∈ u ∧ ContDiffOn ℝ (j : ℕ) (f i) u := by
    intro i
    obtain ⟨u, hu, hon⟩ := ContDiffAt.contDiffOn (hdiff i) le_rfl (by simp)
    obtain ⟨t, htu, ht, hxt⟩ := mem_nhds_iff.mp hu
    exact ⟨t, ht, hxt, hon.mono htu⟩
  choose u hu using hstep
  have huopen : ∀ i, IsOpen (u i) := fun i => (hu i).1
  have hxu : ∀ i, x ∈ u i := fun i => (hu i).2.1
  have huon : ∀ i, ContDiffOn ℝ (j : ℕ) (f i) (u i) := fun i => (hu i).2.2
  let S : Set (Fin m → ℝ) := ⋂ i, u i
  have hSopen : IsOpen S := isOpen_iInter_of_finite (fun i => huopen i)
  have hSnhds : S ∈ 𝓝 x := Filter.iInter_mem.mpr (fun i => (huopen i).mem_nhds (hxu i))
  have hSeq : S =ᶠ[𝓝 x] Set.univ :=
    Filter.eventually_of_mem hSnhds (fun y hy => by simp [hy])
  have hconv : ∀ (F : (Fin m → ℝ) → ℝ) (k : ℕ),
      iteratedFDerivWithin ℝ k F S x = iteratedFDeriv ℝ k F x := fun F k => by
    rw [iteratedFDerivWithin_congr_set hSeq k, iteratedFDerivWithin_univ]
  have hmain := norm_prod_le_within d m j S f x hSopen.uniqueDiffOn (mem_of_mem_nhds hSnhds)
    (fun i => (huon i).mono (Set.iInter_subset u i))
    (fun i => by simpa only [Real.norm_eq_abs] using hval i)
    (fun i k hk1 hk2 => by rw [hconv (f i) k]; exact hjet i k hk1 hk2)
    j le_rfl
  rwa [hconv (fun y => ∏ i, f i y) j] at hmain

theorem jet_prod_bound {m d j : ℕ} (f : Fin d → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (e : Fin j → Fin m)
    (hdiff : ∀ i, ContDiffAt ℝ (j : ℕ) (f i) x)
    (hval : ∀ i, |f i x| ≤ 1)
    (hjet : ∀ i, ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ 1) :
    |iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x (fun k => Pi.single (e k) 1)| ≤ (d : ℝ) ^ j := by
  have hnorm := norm_prod_le f x hdiff hval hjet
  let v : Fin j → (Fin m → ℝ) := fun k => Pi.single (e k) 1
  have hvv : ∀ k, ‖v k‖ = 1 := fun k => by
    simp only [v, Pi.norm_single, norm_one]
  calc |(iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x) v|
      = ‖(iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x) v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x‖ * ∏ k, ‖v k‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ j (fun y => ∏ i, f i y) x‖ := by
        rw [Finset.prod_congr rfl (fun k _ => hvv k), Finset.prod_const_one, mul_one]
    _ ≤ (d : ℝ) ^ j := hnorm

end Work.WilkiesH.Interp
