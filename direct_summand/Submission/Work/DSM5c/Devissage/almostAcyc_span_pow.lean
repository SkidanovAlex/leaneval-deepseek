import Submission.Work.DSMap.Mix2

/-!
# DSM5c — the dévissage `p ↦ p ^ m` for `AlmostAcyc`

Let `W` be a commutative ring, `p` a prime, `ϖ : ℕ → W` a compatible system of `p`-power roots of a
unit multiple of `p` (`ϖ 0 ^ p = p * v`, `ϖ (k+1) ^ p = ϖ k`), and `K` a cochain complex of
`W`-modules in nonnegative degrees with a cocycle coaugmentation `e : W → K^0`.  If the augmented
complex `W → K` is `⇑ϖ`-almost acyclic modulo `p` and the terms of `K` are `p`-torsion-free, then it
is `⇑ϖ`-almost acyclic modulo `p ^ m` for every `m ≥ 0`.

This is the node the M5c design calls the *dévissage* (`sources/dsmap/direct_summand_mix2.md`,
Task 1 (4)); the frozen statement `DSMap.Mix2.area_M5c` needs it because the mod-`p` comparison
`Č(D)/p ≅ Č(D♭)/ϖ♭^p` is available only modulo `p`, while `DSMap.Mix2.area_M5d` consumes
`AlmostAcyc … (p ^ m)` for every `m`.

## The correction of `NOTES.md` §8

`Submission/Work/DSM5c/NOTES.md` §8 claims that the dévissage is *false* as a general lemma, on the
grounds that iterating the mod-`p` clauses produces only the `m`-th **power** `ϖ k ^ m` of the
almost-vector.  That conclusion is wrong:

* iterating the three clauses of `AlmostAcyc` `m` times at a fixed index `k` gives killing by
  `ϖ k ^ (2 * m)` modulo `p ^ m` (two powers of `ϖ k` are accumulated per step);
* the almost-vector can be **re-indexed along the root tower**: for `p ^ n ≥ 2 * m` one has
  `ϖ (k + n) ^ (p ^ n) = ϖ k` and `p ^ n = 2 * m + (p ^ n - 2 * m)`, so multiplying the identity
  by `ϖ (k + n) ^ (p ^ n - 2 * m)` replaces the power `ϖ k ^ (2 * m)` by `ϖ k` itself.

So `ϖ k`-killing modulo `p ^ m` follows for every `k` and `m`; no completeness hypothesis is needed,
and `hreg` (termwise `p`-torsion-freeness) is used only to divide by `p ^ m` inside the iteration.
The workspace's counterexample (`Submission/Work/DSM5c/ProbeDevissage.lean`, NOTES §8) is not a
counterexample: it violates the coaugmentation-cocycle hypothesis `he` (its differential is
`d⁰ = p · id` with `e = id`), and in fact its clause (3) already fails modulo `p` at
`z = 1 ∈ K¹`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Helper

variable {W : Type a} [CommRing W] {M : Type a} [AddCommGroup M] [Module W M]

/-- Membership in `(r) • ⊤` for a principal ideal: `x ∈ (r) • ⊤` iff `x` is a multiple of `r`. -/
theorem mem_span_singleton_smul_top (r : W) (x : M) :
    x ∈ Ideal.span {r} • (⊤ : Submodule W M) ↔ ∃ y : M, r • y = x := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∃ y, r • y = x) hx ?_ ?_
    · intro b hb m _
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
      exact ⟨c • m, by rw [mul_smul]⟩
    · rintro x y ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨(c + d : M), by rw [smul_add]⟩
  · rintro ⟨y, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top

/-- The ideal form: `x ∈ (r)` iff `x` is a multiple of `r`. -/
theorem mem_span_singleton_iff (r x : W) : x ∈ Ideal.span {r} ↔ ∃ y : W, r * y = x := by
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end Helper

section Main

variable {W : Type a} [CommRing W] (p : ℕ) [Fact p.Prime] (ϖ : ℕ → W)

/-- The root-tower identity: `ϖ (k + n) ^ (p ^ n) = ϖ k`. -/
theorem rootTower_pow (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k) (k n : ℕ) :
    ϖ (k + n) ^ p ^ n = ϖ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, pow_succ, mul_comm (p ^ n) p, pow_mul, hroot (k + n)]
    exact ih

/-- Re-indexing along the root tower: `ϖ k` is a multiple of `ϖ (k + n) ^ (2 * m)` as soon as
`p ^ n ≥ 2 * m`. -/
theorem rootTower_reindex (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k) {m n : ℕ} (hn : 2 * m ≤ p ^ n)
    (k : ℕ) : ∃ c : W, ϖ (k + n) ^ (2 * m) * c = ϖ k :=
  ⟨ϖ (k + n) ^ (p ^ n - 2 * m), by
    rw [← pow_add, Nat.add_sub_of_le hn, rootTower_pow p ϖ hroot k n]⟩

/-- **Dévissage `p ↦ p ^ m` for `AlmostAcyc`.** -/
theorem almostAcyc_span_pow (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k)
    (K : CochainComplex (ModuleCat.{a} W) ℕ) (e : ModuleCat.of W W ⟶ K.X 0)
    (he : ∀ w : W, (K.d 0 1).hom (e.hom w) = 0)
    (hK : AlmostAcyc ϖ (Ideal.span {(p : W)}) K e)
    (hreg : ∀ q, IsSMulRegular (K.X q) (p : W)) :
    ∀ m, AlmostAcyc ϖ (Ideal.span {(p : W) ^ m}) K e := by
  have hregPow : ∀ (q n : ℕ), IsSMulRegular (K.X q) ((p : W) ^ n) := fun q n =>
    (hreg q).pow n
  -- ## Clause (1), iterated
  have hC : ∀ m : ℕ, ∀ (i : ℕ) (w : W),
      (∃ z : K.X 0, ((p : W) ^ m) • z = e.hom w) →
      ∃ c : W, ((p : W) ^ m) * c = ϖ i ^ (2 * m) * w := by
    intro m
    induction m with
    | zero => intro i w _; exact ⟨w, by simp⟩
    | succ m ih =>
      intro i w hw
      obtain ⟨z, hz⟩ := hw
      obtain ⟨c, hc⟩ := ih i w ⟨(p : W) • z, by rw [← hz, pow_succ, mul_smul]⟩
      have hker : e.hom c - (p : W) • (ϖ i ^ (2 * m) • z) = 0 := by
        refine hregPow 0 m ?_
        show (p : W) ^ m • (e.hom c - (p : W) • (ϖ i ^ (2 * m) • z)) =
          (p : W) ^ m • (0 : K.X 0)
        have h1 : (p : W) ^ m • e.hom c = ϖ i ^ (2 * m) • e.hom w := by
          rw [← map_smul, smul_eq_mul, hc, ← smul_eq_mul, map_smul]
        have h2 : (p : W) ^ m • ((p : W) • (ϖ i ^ (2 * m) • z)) =
            (p : W) ^ (m + 1) • (ϖ i ^ (2 * m) • z) := by
          rw [pow_succ, mul_smul]
        rw [smul_sub, h1, h2, ← hz, smul_comm (ϖ i ^ (2 * m)) ((p : W) ^ (m + 1)), sub_self,
          smul_zero]
      have hec : e.hom c = (p : W) • (ϖ i ^ (2 * m) • z) := sub_eq_zero.mp hker
      obtain ⟨d, hd⟩ := (mem_span_singleton_iff (p : W) (ϖ i * c)).mp
        (hK.1 c ((mem_span_singleton_smul_top (W := W) (p : W) (e.hom c)).mpr
          ⟨ϖ i ^ (2 * m) • z, hec.symm⟩) i)
      refine ⟨ϖ i * d, ?_⟩
      have e1 : ϖ i ^ (2 * m + 2) * w = ϖ i * (p : W) ^ m * (ϖ i * c) := by
        rw [show ϖ i ^ (2 * m + 2) = ϖ i * ϖ i * ϖ i ^ (2 * m) from by ring,
          show ϖ i * ϖ i * ϖ i ^ (2 * m) * w = (ϖ i * ϖ i) * (ϖ i ^ (2 * m) * w) from by ring,
          ← hc]
        ring
      rw [show 2 * (m + 1) = 2 * m + 2 from by ring, e1, ← hd]
      ring
  -- ## Clause (3), iterated
  have hA : ∀ m : ℕ, ∀ (q i : ℕ) (z : K.X (q + 1)),
      (∃ v : K.X (q + 2), ((p : W) ^ m) • v = (K.d (q + 1) (q + 2)).hom z) →
      ∃ y : K.X q, ∃ v : K.X (q + 1),
        ((p : W) ^ m) • v = ϖ i ^ (2 * m) • z - (K.d q (q + 1)).hom y := by
    intro m
    induction m with
    | zero => intro q i z _; exact ⟨0, ⟨z, by simp⟩⟩
    | succ m ih =>
      intro q i z hz
      obtain ⟨v, hv⟩ := hz
      obtain ⟨y₀, z₁, hz₁⟩ := ih q i z ⟨(p : W) • v, by rw [← hv, pow_succ, mul_smul]⟩
      have hdz₁ : ∃ v' : K.X (q + 2), (p : W) • v' = (K.d (q + 1) (q + 2)).hom z₁ := by
        refine ⟨ϖ i ^ (2 * m) • v, ?_⟩
        refine hregPow (q + 2) m ?_
        show (p : W) ^ m • ((p : W) • (ϖ i ^ (2 * m) • v)) =
          (p : W) ^ m • ((K.d (q + 1) (q + 2)).hom z₁)
        calc (p : W) ^ m • ((p : W) • (ϖ i ^ (2 * m) • v))
            = (p : W) ^ (m + 1) • (ϖ i ^ (2 * m) • v) := by
                rw [pow_succ]
                exact (mul_smul ((p : W) ^ m) (p : W) (ϖ i ^ (2 * m) • v)).symm
          _ = ϖ i ^ (2 * m) • ((p : W) ^ (m + 1) • v) := by rw [smul_comm]
          _ = ϖ i ^ (2 * m) • ((K.d (q + 1) (q + 2)).hom z) := by rw [hv]
          _ = (K.d (q + 1) (q + 2)).hom (ϖ i ^ (2 * m) • z) := (map_smul _ _ _).symm
          _ = (K.d (q + 1) (q + 2)).hom ((p : W) ^ m • z₁ + (K.d q (q + 1)).hom y₀) := by
                rw [hz₁]; abel
          _ = (p : W) ^ m • ((K.d (q + 1) (q + 2)).hom z₁) := by
                rw [map_add, show (K.d (q + 1) (q + 2)).hom ((K.d q (q + 1)).hom y₀) = 0 from by
                  have hdd : (K.d q (q + 1) ≫ K.d (q + 1) (q + 2)) =
                      (0 : K.X q ⟶ K.X (q + 2)) := HomologicalComplex.d_comp_d ..
                  exact congrArg (fun f => f.hom y₀) hdd, add_zero, map_smul]
      obtain ⟨y₁, hy₁⟩ := hK.2.2 q z₁
        ((mem_span_singleton_smul_top (W := W) (p : W)
          ((K.d (q + 1) (q + 2)).hom z₁)).mpr hdz₁) i
      have hv'mem : ϖ i • z₁ - (K.d q (q + 1)).hom y₁ ∈
          Ideal.span {(p : W)} • (⊤ : Submodule W (K.X (q + 1))) := hy₁
      obtain ⟨v', hv'⟩ := (mem_span_singleton_smul_top (p : W)
        (ϖ i • z₁ - (K.d q (q + 1)).hom y₁)).mp hv'mem
      refine ⟨ϖ i ^ 2 • y₀ + (p : W) ^ m • (ϖ i • y₁), ⟨ϖ i • v', ?_⟩⟩
      have key₁ : (p : W) ^ m • (ϖ i • (ϖ i • z₁)) =
          ϖ i ^ (2 * m + 2) • z - (K.d q (q + 1)).hom (ϖ i ^ 2 • y₀) := by
        calc (p : W) ^ m • (ϖ i • (ϖ i • z₁))
            = (p : W) ^ m • (ϖ i ^ 2 • z₁) := by
                rw [show ϖ i • (ϖ i • z₁) = ϖ i ^ 2 • z₁ from by rw [pow_two, smul_smul]]
          _ = ϖ i ^ 2 • ((p : W) ^ m • z₁) := by rw [smul_comm]
          _ = ϖ i ^ 2 • (ϖ i ^ (2 * m) • z - (K.d q (q + 1)).hom y₀) := by rw [hz₁]
          _ = ϖ i ^ (2 * m + 2) • z - (K.d q (q + 1)).hom (ϖ i ^ 2 • y₀) := by
                rw [smul_sub, map_smul,
                  show ϖ i ^ 2 • (ϖ i ^ (2 * m) • z) = ϖ i ^ (2 * m + 2) • z from by
                    rw [show (ϖ i ^ (2 * m + 2)) = ϖ i ^ 2 * ϖ i ^ (2 * m) from by
                      rw [← pow_add]; ring, smul_smul]]
      have key₂ : (p : W) ^ m • (ϖ i • (K.d q (q + 1)).hom y₁) =
          (K.d q (q + 1)).hom ((p : W) ^ m • (ϖ i • y₁)) := by
        rw [smul_smul, smul_smul, map_smul]
      calc (p : W) ^ (m + 1) • (ϖ i • v')
          = (p : W) ^ m • ((p : W) • (ϖ i • v')) := by
              rw [pow_succ]
              exact mul_smul ((p : W) ^ m) (p : W) (ϖ i • v')
        _ = (p : W) ^ m • (ϖ i • ((p : W) • v')) := by
              rw [show (p : W) • (ϖ i • v') = ϖ i • ((p : W) • v') from
                smul_comm (p : W) (ϖ i) v']
        _ = (p : W) ^ m • (ϖ i • (ϖ i • z₁ - (K.d q (q + 1)).hom y₁)) := by rw [hv']
        _ = (p : W) ^ m • (ϖ i • (ϖ i • z₁)) -
              (p : W) ^ m • (ϖ i • (K.d q (q + 1)).hom y₁) := by rw [smul_sub, smul_sub]
        _ = (ϖ i ^ (2 * m + 2) • z - (K.d q (q + 1)).hom (ϖ i ^ 2 • y₀)) -
              (K.d q (q + 1)).hom ((p : W) ^ m • (ϖ i • y₁)) := by rw [key₁, key₂]
        _ = ϖ i ^ (2 * m + 2) • z -
              (K.d q (q + 1)).hom (ϖ i ^ 2 • y₀ + (p : W) ^ m • (ϖ i • y₁)) := by
              rw [map_add, sub_sub]
  -- ## Clause (2), iterated
  have hB : ∀ m : ℕ, ∀ (i : ℕ) (z : K.X 0),
      (∃ v : K.X 1, ((p : W) ^ m) • v = (K.d 0 1).hom z) →
      ∃ w : W, ∃ v : K.X 0, ((p : W) ^ m) • v = ϖ i ^ (2 * m) • z - e.hom w := by
    intro m
    induction m with
    | zero => intro i z _; exact ⟨0, ⟨z, by simp⟩⟩
    | succ m ih =>
      intro i z hz
      obtain ⟨v, hv⟩ := hz
      obtain ⟨w₀, z₁, hz₁⟩ := ih i z ⟨(p : W) • v, by rw [← hv, pow_succ, mul_smul]⟩
      have hdz₁ : ∃ v' : K.X 1, (p : W) • v' = (K.d 0 1).hom z₁ := by
        refine ⟨ϖ i ^ (2 * m) • v, ?_⟩
        refine hregPow 1 m ?_
        show (p : W) ^ m • ((p : W) • (ϖ i ^ (2 * m) • v)) = (p : W) ^ m • ((K.d 0 1).hom z₁)
        calc (p : W) ^ m • ((p : W) • (ϖ i ^ (2 * m) • v))
            = (p : W) ^ (m + 1) • (ϖ i ^ (2 * m) • v) := by
                rw [pow_succ]
                exact (mul_smul ((p : W) ^ m) (p : W) (ϖ i ^ (2 * m) • v)).symm
          _ = ϖ i ^ (2 * m) • ((p : W) ^ (m + 1) • v) := by rw [smul_comm]
          _ = ϖ i ^ (2 * m) • ((K.d 0 1).hom z) := by rw [hv]
          _ = (K.d 0 1).hom (ϖ i ^ (2 * m) • z) := (map_smul _ _ _).symm
          _ = (K.d 0 1).hom ((p : W) ^ m • z₁ + e.hom w₀) := by
                rw [hz₁]; abel
          _ = (p : W) ^ m • ((K.d 0 1).hom z₁) := by
                rw [map_add, he w₀, add_zero, map_smul]
      obtain ⟨w₁, hw₁⟩ := hK.2.1 z₁
        ((mem_span_singleton_smul_top (W := W) (p : W) ((K.d 0 1).hom z₁)).mpr hdz₁) i
      have hw'mem : ϖ i • z₁ - e.hom w₁ ∈
          Ideal.span {(p : W)} • (⊤ : Submodule W (K.X 0)) := hw₁
      obtain ⟨v', hv'⟩ := (mem_span_singleton_smul_top (p : W)
        (ϖ i • z₁ - e.hom w₁)).mp hw'mem
      refine ⟨ϖ i ^ 2 * w₀ + (p : W) ^ m * (ϖ i * w₁), ⟨ϖ i • v', ?_⟩⟩
      have key₁ : (p : W) ^ m • (ϖ i • (ϖ i • z₁)) =
          ϖ i ^ (2 * m + 2) • z - e.hom (ϖ i ^ 2 * w₀) := by
        calc (p : W) ^ m • (ϖ i • (ϖ i • z₁))
            = (p : W) ^ m • (ϖ i ^ 2 • z₁) := by
                rw [show ϖ i • (ϖ i • z₁) = ϖ i ^ 2 • z₁ from by rw [pow_two, smul_smul]]
          _ = ϖ i ^ 2 • ((p : W) ^ m • z₁) := by rw [smul_comm]
          _ = ϖ i ^ 2 • (ϖ i ^ (2 * m) • z - e.hom w₀) := by rw [hz₁]
          _ = ϖ i ^ (2 * m + 2) • z - e.hom (ϖ i ^ 2 * w₀) := by
                rw [smul_sub,
                  show ϖ i ^ 2 • (ϖ i ^ (2 * m) • z) = ϖ i ^ (2 * m + 2) • z from by
                    rw [show (ϖ i ^ (2 * m + 2)) = ϖ i ^ 2 * ϖ i ^ (2 * m) from by
                      rw [← pow_add]; ring, smul_smul],
                  ← map_smul, smul_eq_mul]
      have key₂ : (p : W) ^ m • (ϖ i • e.hom w₁) = e.hom ((p : W) ^ m * (ϖ i * w₁)) := by
        rw [← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]
      calc (p : W) ^ (m + 1) • (ϖ i • v')
          = (p : W) ^ m • ((p : W) • (ϖ i • v')) := by
              rw [pow_succ]
              exact mul_smul ((p : W) ^ m) (p : W) (ϖ i • v')
        _ = (p : W) ^ m • (ϖ i • ((p : W) • v')) := by
              rw [show (p : W) • (ϖ i • v') = ϖ i • ((p : W) • v') from
                smul_comm (p : W) (ϖ i) v']
        _ = (p : W) ^ m • (ϖ i • (ϖ i • z₁ - e.hom w₁)) := by rw [hv']
        _ = (p : W) ^ m • (ϖ i • (ϖ i • z₁)) - (p : W) ^ m • (ϖ i • e.hom w₁) := by
              rw [smul_sub, smul_sub]
        _ = (ϖ i ^ (2 * m + 2) • z - e.hom (ϖ i ^ 2 * w₀)) -
              e.hom ((p : W) ^ m * (ϖ i * w₁)) := by rw [key₁, key₂]
        _ = ϖ i ^ (2 * m + 2) • z -
              e.hom (ϖ i ^ 2 * w₀ + (p : W) ^ m * (ϖ i * w₁)) := by
              rw [map_add, sub_sub]
  -- ## Re-indexing and assembly
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpow : ∀ m : ℕ, 2 * m ≤ p ^ (2 * m + 1) := by
    intro m
    have h1 : 2 * m < 2 ^ (2 * m) := Nat.lt_two_pow_self
    have h2 : 2 ^ (2 * m) ≤ p ^ (2 * m) := Nat.pow_le_pow_left hp2 _
    have h3 : p ^ (2 * m) ≤ p ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans (le_trans h1.le h2) h3
  intro m
  refine ⟨?_, ?_, ?_⟩
  · intro w hw k
    obtain ⟨z, hz⟩ := (mem_span_singleton_smul_top (W := W) ((p : W) ^ m) (e.hom w)).mp hw
    obtain ⟨c, hc⟩ := hC m (k + (2 * m + 1)) w ⟨z, hz⟩
    obtain ⟨c', hc'⟩ := rootTower_reindex p ϖ hroot (hpow m) k
    have hkey : ϖ k * w = (p : W) ^ m * (c' * c) := by
      calc ϖ k * w
          = (ϖ (k + (2 * m + 1)) ^ (2 * m) * c') * w := by rw [hc']
        _ = c' * (ϖ (k + (2 * m + 1)) ^ (2 * m) * w) := by ring
        _ = c' * ((p : W) ^ m * c) := by rw [hc]
        _ = (p : W) ^ m * (c' * c) := by ring
    rw [hkey]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ((p : W) ^ m))
  · intro z hz k
    obtain ⟨v, hv⟩ := (mem_span_singleton_smul_top (W := W) ((p : W) ^ m)
      ((K.d 0 1).hom z)).mp hz
    obtain ⟨w, v', hv'⟩ := hB m (k + (2 * m + 1)) z ⟨v, hv⟩
    obtain ⟨c, hc⟩ := rootTower_reindex p ϖ hroot (hpow m) k
    refine ⟨c * w, ?_⟩
    refine (mem_span_singleton_smul_top (W := W) ((p : W) ^ m) _).mpr ⟨c • v', ?_⟩
    calc (p : W) ^ m • (c • v')
        = c • ((p : W) ^ m • v') := by rw [smul_comm]
      _ = c • (ϖ (k + (2 * m + 1)) ^ (2 * m) • z - e.hom w) := by rw [hv']
      _ = (c * ϖ (k + (2 * m + 1)) ^ (2 * m)) • z - e.hom (c * w) := by
            rw [smul_sub, smul_smul, ← map_smul, smul_eq_mul]
      _ = ϖ k • z - e.hom (c * w) := by rw [mul_comm c, hc]
  · intro q z hz k
    obtain ⟨v, hv⟩ := (mem_span_singleton_smul_top (W := W) ((p : W) ^ m)
      ((K.d (q + 1) (q + 2)).hom z)).mp hz
    obtain ⟨y, v', hv'⟩ := hA m q (k + (2 * m + 1)) z ⟨v, hv⟩
    obtain ⟨c, hc⟩ := rootTower_reindex p ϖ hroot (hpow m) k
    refine ⟨c • y, ?_⟩
    refine (mem_span_singleton_smul_top (W := W) ((p : W) ^ m) _).mpr ⟨c • v', ?_⟩
    calc (p : W) ^ m • (c • v')
        = c • ((p : W) ^ m • v') := by rw [smul_comm]
      _ = c • (ϖ (k + (2 * m + 1)) ^ (2 * m) • z - (K.d q (q + 1)).hom y) := by rw [hv']
      _ = (c * ϖ (k + (2 * m + 1)) ^ (2 * m)) • z -
            (K.d q (q + 1)).hom (c • y) := by
            rw [smul_sub, smul_smul, map_smul]
      _ = ϖ k • z - (K.d q (q + 1)).hom (c • y) := by rw [mul_comm c, hc]

end Main

end Work.DSM5c
