import Mathlib
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.awayComplex
import Submission.Work.DSM5b.awayInDenominator
import Submission.Work.DSM5b.awayIn_eq_zero_pow_mul
import Submission.Work.DSM5b.awayExactFree

/-!
# `Work.DSM5b.honestKillFree` — the honest killing chain, re-derived clash-free

`Work.DSM5b.honestKillingCore` (`Submission/Work/DSM5b/honestKillingCore.lean`) already isolates the
per-cycle honest power killing from the exactness of the `T`-localised complex: it takes `hexact` as
a hypothesis.  Feeding it `Work.DSM5b.awayExactFree` (proved in `Submission/Work/DSM5b/awayExactFree.lean`
under non-clashing names) produces the per-cycle statement **`honestPowerKillingFree`** with the
characteristic / perfectness hypotheses removed — this is the form needed for the *subring* `R₀ ⊆ R`
in the node's support argument (a finitely generated subring of a perfect ring is Noetherian but not
perfect).

`honestKillCoordNoethOfFree` is then the assembly of the *uniform* Noetherian statement from
finiteness + vanishing, verbatim the argument of `Work.DSM5b.honestKillCoordNoeth_of` but with
`honestPowerKillingFree` in place of `Work.DSM5b.honestPowerKillingOf`.

(The duplication with `Submission/Work/DSM5b/honestKillCoordNoeth.lean` is forced by the workspace
name clash: that file imports `awayExact`, and `awayExact.lean` imports `awayPsi.lean`, which
defines a declaration named `Work.DSM5b.psi` — clashing with `CechIsoDefs.psi`, so it cannot be
imported next to the `cechIso` chain that the M5b node needs.)
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

/-- **Per-cycle honest power killing, characteristic-free and clash-free.**  Every cycle of the
honest chart Čech complex in positive degree becomes a boundary after multiplying by some power of
`T`.  Assembled from `Work.DSM5b.honestKillingCore` with
`hexact := Work.DSM5b.awayExactFree`. -/
theorem honestPowerKillingFree {R : Type a} [CommRing R] {ι : Type a} [Finite ι] [DecidableEq ι]
    (t : ι → R) (T : R) (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e)
    (n : ℕ) (z : HCX t (n + 1)) (hz : HCd t (n + 1) z = 0) :
    ∃ N : ℕ, T ^ N • z ∈ LinearMap.range (HCd t n) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- the localised cycle
  have hzL : AWd t T (n + 1) (iotaL t T (n + 1) z) = 0 := by
    rw [← iotaL_HCd t T (n + 1) z, hz]
    exact map_zero _
  obtain ⟨y, hy⟩ := awayExactFree R t T j₀ e hj₀ n (iotaL t T (n + 1) z) hzL
  -- clearing denominators
  have hchoice : ∀ τ : Fin (n + 1) → ι, ∃ kk : ℕ, ∃ cc : ↥(chartRing t (tupRng τ)),
      awayIn t T (tupRng τ) (cc : Localization.Away (tS t (tupRng τ)))
        = (algebraMap R (Localization.Away (T * tS t (tupRng τ))) T) ^ kk * y τ :=
    fun τ => awayIn_denominator t T j₀ e hj₀ (tupRng τ) (y τ)
  choose kk cc hcc using hchoice
  let k : ℕ := Finset.univ.sup kk
  have hkle : ∀ τ, kk τ ≤ k := fun τ => Finset.le_sup (Finset.mem_univ τ)
  -- the honest cochain whose localisation is `T ^ k • y`
  let c : HCX t n := fun τ =>
    algebraMap R ↥(chartRing t (tupRng τ)) (T ^ (k - kk τ)) * cc τ
  have hcy : iotaL t T n c = T ^ k • y := by
    funext τ
    rw [iotaL_apply, Pi.smul_apply, Algebra.smul_def, map_pow]
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, map_mul,
      show awayIn t T (tupRng τ)
          (algebraMap R (Localization.Away (tS t (tupRng τ))) (T ^ (k - kk τ)))
        = algebraMap R (Localization.Away (T * tS t (tupRng τ))) (T ^ (k - kk τ)) from
        liftAway_algebraMap (dvd_mul_left (tS t (tupRng τ)) T) (T ^ (k - kk τ)),
      hcc τ, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hkle τ)]
  -- the difference is in the kernel of the localisation
  have hiota : iotaL t T (n + 1) (T ^ k • z - HCd t n c) = 0 := by
    rw [map_sub, iotaL_HCd, hcy]
    simp only [map_smul, hy, sub_self]
  -- componentwise torsion
  have hcomp : ∀ τ : Fin (n + 1 + 1) → ι,
      ∃ m : ℕ, T ^ m • ((T ^ k • z - HCd t n c) τ) = 0 := by
    intro τ
    have h0 : awayIn t T (tupRng τ)
        (((T ^ k • z - HCd t n c) τ) : Localization.Away (tS t (tupRng τ))) = 0 := by
      have h1 := congrFun hiota τ
      simpa only [Pi.zero_apply, iotaL_apply] using h1
    obtain ⟨m, hm⟩ := awayIn_eq_zero_pow_mul t T (tupRng τ) _ h0
    refine ⟨m, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_smul, Subalgebra.coe_zero, Algebra.smul_def, map_pow]
    exact hm
  let M : ℕ := Finset.univ.sup (fun τ => Classical.choose (hcomp τ))
  have hMle : ∀ τ, Classical.choose (hcomp τ) ≤ M :=
    fun τ => Finset.le_sup (f := fun τ => Classical.choose (hcomp τ)) (Finset.mem_univ τ)
  have hWzero : T ^ M • (T ^ k • z - HCd t n c) = 0 := by
    funext τ
    rw [Pi.smul_apply, Pi.zero_apply]
    calc T ^ M • ((T ^ k • z - HCd t n c) τ)
        = (T ^ (M - Classical.choose (hcomp τ)) * T ^ (Classical.choose (hcomp τ)))
            • ((T ^ k • z - HCd t n c) τ) := by
          rw [← pow_add, Nat.sub_add_cancel (hMle τ)]
      _ = T ^ (M - Classical.choose (hcomp τ))
            • (T ^ (Classical.choose (hcomp τ)) • ((T ^ k • z - HCd t n c) τ)) := by
          rw [mul_smul]
      _ = T ^ (M - Classical.choose (hcomp τ)) • 0 := by
          rw [Classical.choose_spec (hcomp τ)]
      _ = 0 := smul_zero _
  refine ⟨M + k, T ^ M • c, ?_⟩
  rw [map_smul]
  have hz1 : T ^ M • HCd t n c = T ^ M • (T ^ k • z) := by
    have h := hWzero
    rw [smul_sub] at h
    exact (sub_eq_zero.mp h).symm
  rw [hz1, smul_smul, ← pow_add]

/-- **The uniform Noetherian statement from finiteness and vanishing.**

`hfin` is the finiteness input: in each positive degree, finitely many cycles span the cohomology
modulo boundaries.  `hvan` is the vanishing input in degrees `≥ ♯ι`.  The conclusion is the uniform
honest killing: one power `T ^ N` kills every positive-degree cycle at once. -/
theorem honestKillCoordNoethOfFree {R : Type a} [CommRing R] {ι : Type a} [Finite ι] [DecidableEq ι]
    (t : ι → R) (T : R) (j₀ : ι) (e : ℕ) (hj₀ : t j₀ = T ^ e)
    (hfin : ∀ q : ℕ, ∃ (k : ℕ) (f : Fin k → HCX t (q + 1)),
      (∀ i, HCd t (q + 1) (f i) = 0) ∧
      ∀ z : HCX t (q + 1), HCd t (q + 1) z = 0 →
        ∃ c : Fin k → R, ∃ y : HCX t q, z = (∑ i, c i • f i) + HCd t q y)
    (hvan : ∀ n : ℕ, Nat.card ι ≤ n + 1 → ∀ z : HCX t (n + 1),
      HCd t (n + 1) z = 0 → z ∈ LinearMap.range (HCd t n)) :
    ∃ N : ℕ, ∀ (n : ℕ) (z : HCX t (n + 1)),
      HCd t (n + 1) z = 0 → T ^ N • z ∈ LinearMap.range (HCd t n) := by
  classical
  have hdeg : ∀ q : ℕ, ∃ N : ℕ, ∀ z : HCX t (q + 1),
      HCd t (q + 1) z = 0 → T ^ N • z ∈ LinearMap.range (HCd t q) := by
    intro q
    obtain ⟨k, f, hfcyc, hfgen⟩ := hfin q
    choose N hN using fun i : Fin k => honestPowerKillingFree t T j₀ e hj₀ q (f i) (hfcyc i)
    refine ⟨Finset.univ.sup N, ?_⟩
    intro z hz
    obtain ⟨c, y, hy⟩ := hfgen z hz
    have hgen : ∀ i : Fin k, T ^ (Finset.univ.sup N) • f i ∈ LinearMap.range (HCd t q) := by
      intro i
      have hle : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
      have hi := hN i
      have hsplit : T ^ (Finset.univ.sup N) • f i
          = T ^ (Finset.univ.sup N - N i) • (T ^ (N i) • f i) := by
        have hpow : T ^ (Finset.univ.sup N)
            = T ^ (Finset.univ.sup N - N i) * T ^ (N i) := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        rw [hpow, mul_smul]
      rw [hsplit]
      exact Submodule.smul_mem _ _ hi
    have hsum : T ^ (Finset.univ.sup N) • (∑ i, c i • f i)
        = ∑ i, c i • (T ^ (Finset.univ.sup N) • f i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [smul_comm])
    rw [hy, smul_add, hsum]
    refine Submodule.add_mem _ (Submodule.sum_mem _ (fun i _ => ?_)) ?_
    · exact Submodule.smul_mem _ _ (hgen i)
    · rw [← map_smul]
      exact LinearMap.mem_range_self _ _
  refine ⟨(Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q)), ?_⟩
  intro n z hz
  by_cases hn : Nat.card ι ≤ n + 1
  · exact Submodule.smul_mem _ _ (hvan n hn z hz)
  · have hmem : n ∈ Finset.range (Nat.card ι) := Finset.mem_range.mpr (by omega)
    have hle : Classical.choose (hdeg n) ≤
        (Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q)) :=
      Finset.le_sup (f := fun q => Classical.choose (hdeg q)) hmem
    have hch := Classical.choose_spec (hdeg n) z hz
    have hsplit : T ^ ((Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q))) • z
        = T ^ ((Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q))
              - Classical.choose (hdeg n)) • (T ^ Classical.choose (hdeg n) • z) := by
      have hpow : T ^ ((Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q)))
          = T ^ ((Finset.range (Nat.card ι)).sup (fun q => Classical.choose (hdeg q))
              - Classical.choose (hdeg n)) * T ^ Classical.choose (hdeg n) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      rw [hpow, mul_smul]
    rw [hsplit]
    exact Submodule.smul_mem _ _ hch

end Work.DSM5b
