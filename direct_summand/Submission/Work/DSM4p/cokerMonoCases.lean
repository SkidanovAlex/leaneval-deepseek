import Mathlib
import Submission.Work.DSM4p.cokerP_pow
import Submission.Work.DSM4p.Chart

/-!
# DSM4p — the two cases of the monomial cokernel estimate

`Work.DSM4p.cokerMonoCases` is the *disjunctive* form of the two-case monomial computation
`Work.DSM4p.cokerP_mono_pow` (`Submission/Work/DSM4p/cokerP_pow.lean`): for root systems `G`, `T`
over a perfect ring `R` of characteristic `p`, a level shift `c ≥ p^(k+1)·m` and any `b0 : R`,
the element

  `T k · G k · b0 · x_J(N + c)^I`

of the ambient ring `R[1/G 0]` is either in the image of `R` or is `(T 0)^(p·m)` times an element
of the `N`-th chart level `chartLevel hG T N`.  Where `cokerP_mono_pow` only asserts a *sum*
decomposition `b + (T 0)^(p·m)·s`, the point here is that the two witnesses can be taken
disjointly: whichever of Bhatt's two cases applies determines which of the two alternatives holds.

The two cases are the same as in `cokerP_mono`/`cokerP_mono_pow`:

* `I·p^k < p^J` (Bhatt's second case): then `k ≤ J` and `I ≤ p^(J-k)`, so the fractional power
  `G 0^{1/p^k - I/p^J} = G J^{p^(J-k) - I}` occurring in the element is a genuine power and the
  element is `b0 · T J^{p^(J-k) + (N+c)I} · G J^{p^(J-k) - I} ∈ R`;
* `p^J ≤ I·p^k` (Bhatt's first case): writing `L := max k J` and
  `e := p^(L-k) + c·I·p^(L-J) - p·m·p^L` (nonnegative by `caseA_bound`), one has
  `T k · T J^(c·I) = (T 0)^(p·m) · T L^e`, hence the element is
  `(T 0)^(p·m) · (b0 · G k · T L^e · x_J(N)^I)` with the second factor in `chartLevel hG T N`.
-/

namespace Work.DSM4p

theorem cokerMonoCases {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] {G T : ℕ → R} (hG : Work.DSM4p.IsRootSystem p G)
    (hT : Work.DSM4p.IsRootSystem p T) (k m c N J I : ℕ) (hc : p ^ (k + 1) * m ≤ c)
    (b0 : R) :
    (∃ b : R, algebraMap R (Work.DSM4p.ChartAmbient G) (T k * G k) *
        (algebraMap R (Work.DSM4p.ChartAmbient G) b0 *
          (Work.DSM4p.chartGen hG T (N + c) J) ^ I) =
        algebraMap R (Work.DSM4p.ChartAmbient G) b)
    ∨ (∃ s ∈ Work.DSM4p.chartLevel hG T N,
        algebraMap R (Work.DSM4p.ChartAmbient G) (T k * G k) *
          (algebraMap R (Work.DSM4p.ChartAmbient G) b0 *
            (Work.DSM4p.chartGen hG T (N + c) J) ^ I) =
          algebraMap R (Work.DSM4p.ChartAmbient G) (T 0 ^ (p * m)) * s) := by
  rcases Nat.eq_zero_or_pos I with hI0 | hIpos
  · -- `I = 0`: the element is `T k · G k · b0`, a base element.
    subst hI0
    refine Or.inl ⟨b0 * (T k * G k), ?_⟩
    rw [pow_zero, mul_one, ← map_mul]
    congr 1
    ring
  · by_cases hcase : I * p ^ k < p ^ J
    · -- ## Bhatt's second case : `I·p^k < p^J`, the element lies in `R`
      have hkJ : k ≤ J := by
        by_contra h
        have h1 : p ^ J < p ^ k := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (not_le.mp h)
        have h2 : p ^ k ≤ I * p ^ k := by
          calc p ^ k = 1 * p ^ k := (one_mul _).symm
            _ ≤ I * p ^ k := Nat.mul_le_mul_right _ hIpos
        exact absurd hcase (not_lt.mpr (le_trans h1.le h2))
      have hIle : I ≤ p ^ (J - k) := by
        have h3 : p ^ J = p ^ (J - k) * p ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkJ]
        rw [h3] at hcase
        exact le_of_lt (lt_of_mul_lt_mul_right hcase (Nat.zero_le _))
      have hunit : chartUnit hG k * (chartUnit hG J ^ I)⁻¹ =
          chartUnit hG J ^ (p ^ (J - k) - I) := by
        rw [← mul_right_cancel_iff (a := chartUnit hG J ^ I)]
        rw [mul_assoc, inv_mul_cancel, mul_one,
          mul_comm (chartUnit hG J ^ (p ^ (J - k) - I)) (chartUnit hG J ^ I),
          ← pow_add, Nat.add_sub_cancel' hIle]
        exact (chartUnit_pow_pow hG hkJ).symm
      have hkey : algebraMap R (ChartAmbient G) (G k) * ↑((chartUnit hG J ^ I)⁻¹) =
          algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I)) := by
        rw [← chartUnit_val hG k, ← Units.val_mul, hunit, Units.val_pow_eq_pow_val,
          chartUnit_val, ← map_pow]
      have htk : T k = T J ^ p ^ (J - k) := (rootSystem_pow_pow hT hkJ).symm
      have hcomb : algebraMap R (ChartAmbient G) (T k) *
            algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I)) =
          algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) := by
        rw [← map_mul, htk, ← pow_add]
      refine Or.inl ⟨b0 * T J ^ (p ^ (J - k) + (N + c) * I) * G J ^ (p ^ (J - k) - I), ?_⟩
      rw [map_mul, chartGen_pow_eq hG T (N + c) J I]
      calc
        algebraMap R (ChartAmbient G) (T k) * algebraMap R (ChartAmbient G) (G k) *
            (algebraMap R (ChartAmbient G) b0 *
              (algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I)) *
                ↑((chartUnit hG J ^ I)⁻¹)))
          = (algebraMap R (ChartAmbient G) (T k) *
              algebraMap R (ChartAmbient G) (T J ^ ((N + c) * I))) *
              (algebraMap R (ChartAmbient G) b0 *
                (algebraMap R (ChartAmbient G) (G k) *
                  ↑((chartUnit hG J ^ I)⁻¹))) := by ring
        _ = algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
              (algebraMap R (ChartAmbient G) b0 *
                (algebraMap R (ChartAmbient G) (G k) *
                  ↑((chartUnit hG J ^ I)⁻¹))) := by rw [hcomb]
        _ = algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
              (algebraMap R (ChartAmbient G) b0 *
                algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I))) := by rw [hkey]
        _ = algebraMap R (ChartAmbient G)
              (b0 * T J ^ (p ^ (J - k) + (N + c) * I) * G J ^ (p ^ (J - k) - I)) := by
              rw [show algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I)) *
                    (algebraMap R (ChartAmbient G) b0 *
                      algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I)))
                  = (algebraMap R (ChartAmbient G) b0 *
                      algebraMap R (ChartAmbient G) (T J ^ (p ^ (J - k) + (N + c) * I))) *
                      algebraMap R (ChartAmbient G) (G J ^ (p ^ (J - k) - I))
                  from by ring,
                ← map_mul, ← map_mul]
    · -- ## Bhatt's first case : `p^J ≤ I·p^k`, the element is `(T 0)^(p·m)` times level `N`
      have hge : p ^ J ≤ I * p ^ k := le_of_not_gt hcase
      set L : ℕ := max k J with hLdef
      have hkL : k ≤ L := by rw [hLdef]; exact le_max_left k J
      have hJL : J ≤ L := by rw [hLdef]; exact le_max_right k J
      have hbound : p * m * p ^ L ≤ p ^ (L - k) + c * I * p ^ (L - J) :=
        caseA_bound hJL hge hc
      set e : ℕ := p ^ (L - k) + c * I * p ^ (L - J) - p * m * p ^ L with hedef
      have htk : T k = T L ^ p ^ (L - k) := (rootSystem_pow_pow hT hkL).symm
      have htJ : T J = T L ^ p ^ (L - J) := (rootSystem_pow_pow hT hJL).symm
      have hT0L : T L ^ p ^ L = T 0 := hT.pow_pow_zero L
      have hexp : p ^ (L - k) + c * I * p ^ (L - J) = e + p * m * p ^ L := by
        rw [hedef]; exact (Nat.sub_add_cancel hbound).symm
      have hchain : T k * T J ^ (c * I) = T 0 ^ (p * m) * T L ^ e := by
        calc T k * T J ^ (c * I)
            = T L ^ p ^ (L - k) * (T L ^ p ^ (L - J)) ^ (c * I) := by rw [htk, htJ]
          _ = T L ^ p ^ (L - k) * T L ^ (p ^ (L - J) * (c * I)) := by rw [← pow_mul]
          _ = T L ^ (p ^ (L - k) + p ^ (L - J) * (c * I)) := by rw [← pow_add]
          _ = T L ^ (e + p * m * p ^ L) := by
                congr 1
                rw [show p ^ (L - J) * (c * I) = c * I * p ^ (L - J) from by ring, hexp]
          _ = T L ^ (p * m * p ^ L) * T L ^ e := by rw [pow_add]; ring
          _ = (T L ^ p ^ L) ^ (p * m) * T L ^ e := by
                rw [show (T L ^ p ^ L) ^ (p * m) = T L ^ (p * m * p ^ L) from by
                  rw [← pow_mul]; congr 1; ring]
          _ = T 0 ^ (p * m) * T L ^ e := by rw [hT0L]
      have hchain' : algebraMap R (ChartAmbient G) (T k) *
            algebraMap R (ChartAmbient G) (T J ^ (c * I)) =
          algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
            algebraMap R (ChartAmbient G) (T L ^ e) := by
        calc algebraMap R (ChartAmbient G) (T k) * algebraMap R (ChartAmbient G) (T J ^ (c * I))
            = algebraMap R (ChartAmbient G) (T k * T J ^ (c * I)) := by rw [map_mul]
          _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m) * T L ^ e) := by rw [hchain]
          _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              algebraMap R (ChartAmbient G) (T L ^ e) := by rw [map_mul]
      have hcomb2 : algebraMap R (ChartAmbient G) (T L ^ e) *
            (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0) =
          algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) := by
        rw [← map_mul, ← map_mul]
        congr 1
        ring
      refine Or.inr ⟨algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) *
        (chartGen hG T N J) ^ I,
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (chartGen_mem hG T N J) I), ?_⟩
      calc
        algebraMap R (ChartAmbient G) (T k * G k) *
            (algebraMap R (ChartAmbient G) b0 * (chartGen hG T (N + c) J) ^ I)
          = (algebraMap R (ChartAmbient G) (T k) *
              algebraMap R (ChartAmbient G) (T J ^ (c * I))) *
              (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0 *
                (chartGen hG T N J) ^ I) := by
              rw [map_mul, chartGen_pow_add_level hG T N c J I]; ring
        _ = (algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              algebraMap R (ChartAmbient G) (T L ^ e)) *
              (algebraMap R (ChartAmbient G) (G k) * algebraMap R (ChartAmbient G) b0 *
                (chartGen hG T N J) ^ I) := by rw [hchain']
        _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              (algebraMap R (ChartAmbient G) (T L ^ e) *
                (algebraMap R (ChartAmbient G) (G k) *
                  algebraMap R (ChartAmbient G) b0) *
                  (chartGen hG T N J) ^ I) := by ring
        _ = algebraMap R (ChartAmbient G) (T 0 ^ (p * m)) *
              (algebraMap R (ChartAmbient G) (b0 * G k * T L ^ e) *
                (chartGen hG T N J) ^ I) := by rw [hcomb2]

end Work.DSM4p
