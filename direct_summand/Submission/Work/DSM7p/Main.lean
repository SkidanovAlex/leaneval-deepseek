import Submission.Work.DSM7p.Basic
import Submission.Work.DSM7p.Krull
import Submission.Work.DSM7p.valIdeal_map
import Submission.Work.DSM7p.modSplit_of_tower
import Submission.Work.DSM7p.modSplit_bot_of_forall_maximal
import Submission.Work.DSM7p.exists_mul_pow_eq
import Submission.Work.DSREG.Main

/-!
# DSM7p — the delivery: `DSMap.Mix2.area_M7p` (M7p of the MIX2 design)

The deliverable of this subproject is `DSMap.Mix2.area_M7p_proved`, whose type is identical to the
frozen interface `DSMap.Mix2.area_M7p` of `Submission/Work/DSMap/Mix2.lean` (the `M7p` node of
`sources/dsmap/direct_summand_mix2.md`), proved sorry-free and axiom-clean.

## What it says

`A` is a complete regular local ring of mixed characteristic `(0,p)`; `P` is a bounded-above complex
of finite free `A`-modules with a coaugmentation `ε : A → P⁰` which is a cocycle; `B` is a
faithfully flat perfectoid `A`-algebra; `g ∈ A` is not divisible by `p` and admits a compatible
system of `p`-power roots `gr` in `B`; `D` is a tower of `B`-algebras which is a *pro-uniform
quantitative Riemann extension* of `B` (`IsQRETp`); and `ε` becomes almost split over every `D n`
modulo every `p ^ m`, with value `(QD n).ϖ k`.  Conclusion: `ε` splits honestly over `A`
(`ModSplit P ε (RingHom.id A) ⊥ 1`), i.e. the direct-summand theorem holds for this model.

## Proof (Bhatt, arXiv:1608.08882, §4, proof of `thm:DSC`)

Everything is phrased through the value ideal `valIdeal P ε ψ I = {c | ModSplit P ε ψ I c}`.

1. (`Work.DSM7p.modSplit_of_tower`) For every `m` and `k`, the almost-element
   `(Q.ϖ k)^3 * (gr k)^2` lies in the value ideal over `B` modulo `p^m`: transport the splittings
   over `D (2c)` down to `B` along the cokernel clause of `IsQRETp` and correct with the kernel
   clause.
2. (`Work.DSM7p.valIdeal_map`) The value ideal over `B` is the extension of the value ideal over
   `A`, since `B` is flat over `A` and `P⁰`, `P⁻¹` are finite free.
3. (Krull) If `1` were *not* a value modulo `p ^ m`, the value ideal `J` would be a proper ideal and
   Krull's intersection theorem would give `K` with `p^2 * g ∉ J ^ K`; raising the almost-element
   of (1) to the `K`-th power gives (via `(ϖ k)^{p^k} = ϖ 0`, `(ϖ 0)^p = p * v`,
   `(gr k)^{p^k} = g` — this is `Work.DSM7p.exists_mul_pow_eq`) a `B`-multiple of
   `algebraMap (p^2 * g)`, whence `p^2 * g ∈ J ^ K` by faithful flatness
   (`Ideal.comap_map_eq_self_of_faithfullyFlat`) — a contradiction.
4. Hence `1` is a value modulo every `p ^ m`, therefore modulo every power of the maximal ideal
   (`p ∈ 𝔪` as the residue field has characteristic `p`), and
   a Krull step for finitely generated modules over a Noetherian local ring
   (`Work.DSM7p.modSplit_bot_of_forall_maximal`; an independent proof of the same statement is
   `Work.DSM7p.modSplit_bot_of_forall_maximal_alt` in `Lift.lean`) upgrades this to the honest splitting modulo `⊥`.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits Opposite
open scoped TensorProduct

namespace DSMap.Mix2

open DSMap DSMap.Mix

universe a

/-- `DSMap.Mix2.area_M7p` (Bhatt Thm 4.4/5.1 assembly, model level), proved. -/
theorem area_M7p_proved (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (hP : IsBddFinFree P) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    (B : Type a) [CommRing B] [Algebra A B] (Q : PerfectoidData p B) [Module.FaithfullyFlat A B]
    (g : A) (hg : g ∉ Ideal.span {(p : A)}) (gr : ℕ → B) (hgr0 : gr 0 = algebraMap A B g)
    (hgr : ∀ k, gr (k + 1) ^ p = gr k) (D : ℕ → Type a) [∀ n, CommRing (D n)]
    [∀ n, Algebra B (D n)] (QD : ∀ n, PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n)
    (hQD : ∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)) (hq : IsQRETp p B Q.ϖ gr D tr)
    (hsplit : ∀ n m k, ModSplit P ε ((algebraMap B (D n)).comp (algebraMap A B))
      (Ideal.span {(p : D n) ^ m}) ((QD n).ϖ k)) :
    ModSplit P ε (RingHom.id A) ⊥ 1 := by
  haveI : IsDomain A := DSMap.area_REG_proved A
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hgnz : g ≠ 0 := by
    intro h; apply hg; rw [h]; exact Ideal.zero_mem _
  have hp2g : (p : A) ^ 2 * g ≠ 0 := mul_ne_zero (pow_ne_zero 2 hp0) hgnz
  have hp_mem : (p : A) ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_natCast]
    exact CharP.cast_eq_zero (ResidueField A) p
  -- Step 1: modulo every `p ^ m` the unit is a value.
  have key : ∀ m : ℕ, (1 : A) ∈ Work.DSM7p.valIdeal P ε (RingHom.id A)
      (Ideal.span {(p : A) ^ m}) := by
    intro m
    by_contra h1
    set J : Ideal A := Work.DSM7p.valIdeal P ε (RingHom.id A) (Ideal.span {(p : A) ^ m}) with hJ
    have hJne : J ≠ ⊤ := fun h => h1 (h ▸ Submodule.mem_top)
    obtain ⟨K, hK, hKp⟩ := Work.DSM7p.exists_pow_notMem_two_mul_le J hJne p hp2 hp2g
    have hz : (Q.ϖ K) ^ 3 * (gr K) ^ 2 ∈
        Work.DSM7p.valIdeal P ε (algebraMap A B) (Ideal.span {(p : B) ^ m}) :=
      (Work.DSM7p.mem_valIdeal _ _ _ _ _).mpr
        (Work.DSM7p.modSplit_of_tower P ε hP p B Q g gr hgr0 D QD tr hQD hq hsplit m K)
    have hspan : (Ideal.span {(p : A) ^ m}).map (algebraMap A B) =
        Ideal.span {(p : B) ^ m} := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
    rw [← hspan, Work.DSM7p.valIdeal_map P ε hP (Ideal.span {(p : A) ^ m})] at hz
    have hzK : ((Q.ϖ K) ^ 3 * (gr K) ^ 2) ^ K ∈ (J ^ K).map (algebraMap A B) := by
      rw [Ideal.map_pow]
      exact Ideal.pow_mem_pow hz K
    obtain ⟨c, hc⟩ := Work.DSM7p.exists_mul_pow_eq p Q g gr hgr0 hgr K hKp
    have hAlg : algebraMap A B ((p : A) ^ 2 * g) ∈ (J ^ K).map (algebraMap A B) := by
      rw [← hc]
      exact Ideal.mul_mem_right c _ hzK
    have hfin : (p : A) ^ 2 * g ∈ J ^ K := by
      have hmem := Ideal.mem_comap.mpr hAlg
      rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
    exact hK hfin
  -- Step 2: the same modulo every power of the maximal ideal.
  have hmax : ∀ k : ℕ, ModSplit P ε (RingHom.id A) ((maximalIdeal A) ^ k) 1 := by
    intro k
    have hle : Ideal.span {(p : A) ^ k} ≤ (maximalIdeal A) ^ k :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.pow_mem_pow hp_mem k))
    exact (Work.DSM7p.mem_valIdeal P ε (RingHom.id A) ((maximalIdeal A) ^ k) 1).mpr
      (Work.DSM7p.valIdeal_mono P ε (RingHom.id A) hle (key k))
  -- Step 3: lift to the honest splitting.
  exact Work.DSM7p.modSplit_bot_of_forall_maximal P ε hP hmax

/-- The delivered result has exactly the type of the frozen `DSMap.Mix2.area_M7p`. -/
example : type_of% (@area_M7p_proved.{a}) = type_of% (@area_M7p.{a}) := rfl

end DSMap.Mix2
