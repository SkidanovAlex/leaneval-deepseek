import Mathlib
import Submission.NK.NUV2.TowerRank.exists_surjective_of_le_dualRank
import Submission.NK.NUV2.ArtinBridge.dualConnectedStep
import Submission.NK.NUV2.ArtinBridge.compactSpace_ideleClassGroup_quot_connectedComponent

/-!
# From a `ℤ_2`-rank bound on the dual of `C_K` to a `ℤ_2`-tower of open subgroups

This file proves `NK.NUV2.TowerRank.exists_nested_subgroups_of_le_dualRank`, the
"*rank* `⟹` *`ℤ_2`-tower*" half of the elementary duality of `Submission/Work/NUV2/TowerRank/NOTES.md`
§1(b)–(c), for the idèle class group `C_K = 𝕀 K ⧸ Kˣ` of a number field `K`:

if `r ≤ dualRank C_K 2 = rank_{ℤ_2} Hom_cts(C_K, ℤ_2)`, then `C_K` admits a **nested tower of open
subgroups**

`C_K ⊇ U 0 ⊇ U 1 ⊇ U 2 ⊇ ⋯`,  `U (n+1) ≤ U n`,  with `C_K ⧸ U n ≃* (ℤ/2^n)^r` for every `n`.

The construction is the classical one: from the rank bound one gets `r` continuous characters
`χ_1, …, χ_r : C_K → ℤ_2` whose joint evaluation is **surjective**
(`NK.NUV2.TowerRank.exists_surjective_of_le_dualRank` — Shimizu's Lemma 4f.1, §1(b) of the NOTES);
the `n`-th subgroup is then the kernel of the composite

`C_K --χ--> ℤ_2^r --(mod 2^n)--> (ℤ/2^n)^r`,

which is open because the target is discrete, and whose quotient is `(ℤ/2^n)^r` because the composite
is surjective.  The three structural facts used are

* `C_K` is *not* compact (its content is unbounded); what is compact is the totally disconnected
  quotient `C_K ⧸ C_K⁰`, and continuous `ℤ_2`-valued characters kill the connected component
  `C_K⁰`: `NK.NUV2.ArtinBridge.dualConnectedStep` (so the rank bound transfers to the quotient)
  and `NK.NUV2.ArtinBridge.compactSpace_ideleClassGroup_quot_connectedComponent`;
* `ℤ_2 → ZMod (2^n)` is surjective, with kernel `2^n ℤ_2` (`PadicInt.toZModPow`,
  `PadicInt.ker_toZModPow`), compatible with the reductions along the tower;
* `2^n ℤ_2` is *open* in `ℤ_2` (it is the closed ball of radius `2^{-n}`, an open ball in an
  ultrametric space), which is what makes `U n` open.

Everything else is bookkeeping about `Additive`/`Multiplicative` wrappers and the quotient
isomorphism `G ⧸ ker f ≃* H` for a surjective `f`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.NUV2.TowerRank

open scoped Topology

/-! ## Three elementary lemmas about `ℤ_[p] → ZMod (p ^ n)` -/

/-- **`ℤ_[p] → ZMod (p^n)` is surjective.**  Every element of `ZMod (p^n)` is the image of an
integer, and integers map to their residue class. -/
theorem towerRank_toZModPow_surjective (p n : ℕ) [Fact p.Prime] :
    Function.Surjective (PadicInt.toZModPow (p := p) n) := by
  intro y
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (n := p ^ n) y
  exact ⟨(m : ℤ_[p]), by rw [map_intCast, hm]⟩

/-- **The reductions along the `ℤ_[p]`-tower are compatible**: `toZModPow n` factors through
`toZModPow (n+1)` via `ZMod.castHom`, so an element killed at level `n + 1` is killed at level `n`.
This is what makes the kernels of the level maps *decreasing*. -/
theorem towerRank_toZModPow_eq_zero_of_succ {p : ℕ} [Fact p.Prime] (n : ℕ) {a : ℤ_[p]}
    (h : PadicInt.toZModPow (p := p) (n + 1) a = 0) :
    PadicInt.toZModPow (p := p) n a = 0 := by
  have h1 := congrFun (congrArg (fun f : ℤ_[p] →+* ZMod (p ^ n) => ⇑f)
    (PadicInt.zmod_cast_comp_toZModPow (p := p) n (n + 1) (Nat.le_succ n))) a
  simp only [RingHom.coe_comp, Function.comp_apply] at h1
  rw [← h1, h, map_zero]

/-- **`p^n ℤ_[p]` is open in `ℤ_[p]`.**  By `PadicInt.norm_le_pow_iff_mem_span_pow` it is the set of
elements of norm at most `p^{-n}`, i.e. the closed ball of radius `p^{-n} ≠ 0`, and closed balls of
positive radius are open in a non-archimedean metric space.  (For `n = 0` both sides are
everything.) -/
theorem towerRank_isOpen_span_pow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen (((Ideal.span {((p : ℤ_[p]) ^ n)} : Ideal ℤ_[p]) : Set ℤ_[p])) := by
  have hset : (((Ideal.span {((p : ℤ_[p]) ^ n)} : Ideal ℤ_[p]) : Set ℤ_[p]))
      = Metric.ball (0 : ℤ_[p]) ((p : ℝ) ^ ((1 : ℤ) - (n : ℤ))) := by
    ext x
    rw [SetLike.mem_coe, Metric.mem_ball, dist_zero_right,
      PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one,
      show (1 : ℤ) - (n : ℤ) - 1 = -(n : ℤ) by ring]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [hset]
  exact Metric.isOpen_ball

/-! ## The tower -/

theorem exists_nested_subgroups_of_le_dualRank {K : Type} [Field K] [NumberField K] (r : ℕ)
    (h : (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.GlobalCFT.IdeleClassGroup K) 2) :
    ∃ U : ℕ → Subgroup (NK.GlobalCFT.IdeleClassGroup K),
      (∀ n, U (n+1) ≤ U n) ∧
      (∀ n, IsOpen ((U n : Set (NK.GlobalCFT.IdeleClassGroup K)))) ∧
      (∀ n, Nonempty ((NK.GlobalCFT.IdeleClassGroup K ⧸ U n) ≃*
        Multiplicative (Fin r → ZMod (2^n)))) := by
  classical
  -- ### The totally disconnected quotient `C_K ⧸ C_K⁰`
  let C0 : Subgroup (NK.GlobalCFT.IdeleClassGroup K) :=
    Subgroup.connectedComponentOfOne (NK.GlobalCFT.IdeleClassGroup K)
  haveI hC0normal : C0.Normal := Subgroup.normal_of_isMulCommutative C0
  haveI hC0closed : IsClosed (C0 : Set (NK.GlobalCFT.IdeleClassGroup K)) :=
    isClosed_connectedComponent
  haveI hC0compact : CompactSpace (NK.GlobalCFT.IdeleClassGroup K ⧸ C0) :=
    NK.NUV2.ArtinBridge.compactSpace_ideleClassGroup_quot_connectedComponent
  -- the rank bound only sees the quotient by the connected component
  have hrank : (r : Cardinal) ≤
      NK.RankTheoryDeep.dualRank (NK.GlobalCFT.IdeleClassGroup K ⧸ C0) 2 := by
    obtain ⟨e⟩ := NK.NUV2.ArtinBridge.dualConnectedStep K 2
    rw [NK.RankTheoryDeep.dualRank] at h
    rw [NK.RankTheoryDeep.dualRank]
    rw [e.rank_eq] at h
    exact h
  -- ### `r` continuous characters of the quotient whose joint evaluation is surjective
  obtain ⟨χ, hχ⟩ := NK.NUV2.TowerRank.exists_surjective_of_le_dualRank
    (G := NK.GlobalCFT.IdeleClassGroup K ⧸ C0) (ℓ := 2) (r := r) hrank
  -- ### the resulting characters of `C_K`, additively
  let Φ : Additive (NK.GlobalCFT.IdeleClassGroup K) →+ (Fin r → PadicInt 2) :=
    { toFun := fun x => fun i =>
        (χ i : Additive (NK.GlobalCFT.IdeleClassGroup K ⧸ C0) →+ PadicInt 2)
          (MonoidHom.toAdditive (QuotientGroup.mk' C0) x)
      map_zero' := by funext i; simp
      map_add' := by intro a b; funext i; simp }
  have hΦsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨y, hy⟩ := hχ v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C0 y
    refine ⟨Additive.ofMul x, ?_⟩
    funext i
    exact congrFun hy i
  have hπcont : Continuous ⇑(QuotientGroup.mk' C0 : NK.GlobalCFT.IdeleClassGroup K →*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ C0)) := by
    rw [QuotientGroup.coe_mk']
    exact QuotientGroup.continuous_mk
  have hΦcont : Continuous Φ := by
    rw [continuous_pi_iff]
    intro i
    exact (χ i).2.comp (hπcont.comp continuous_toMul)
  -- ### the level maps `C_K → (ℤ/2^n)^r`
  let Φn : (n : ℕ) → Additive (NK.GlobalCFT.IdeleClassGroup K) →+ (Fin r → ZMod (2 ^ n)) :=
    fun n =>
      { toFun := fun x => fun i => PadicInt.toZModPow (p := 2) n (Φ x i)
        map_zero' := by funext i; simp
        map_add' := by intro a b; funext i; simp }
  have hΦn_apply : ∀ (n : ℕ) (x : Additive (NK.GlobalCFT.IdeleClassGroup K)),
      (Φn n x : Fin r → ZMod (2 ^ n)) = fun i => PadicInt.toZModPow (p := 2) n (Φ x i) :=
    fun n x => rfl
  have hΦnsurj : ∀ n, Function.Surjective (Φn n) := by
    intro n y
    choose a ha using fun i => towerRank_toZModPow_surjective 2 n (y i)
    obtain ⟨x, hx⟩ := hΦsurj a
    refine ⟨x, ?_⟩
    rw [hΦn_apply]
    funext i
    show PadicInt.toZModPow (p := 2) n (Φ x i) = y i
    rw [congrFun hx i]
    exact ha i
  let Ψ : (n : ℕ) → NK.GlobalCFT.IdeleClassGroup K →*
      Multiplicative (Fin r → ZMod (2 ^ n)) :=
    fun n =>
      { toFun := fun x => Multiplicative.ofAdd (Φn n (Additive.ofMul x))
        map_one' := by
          rw [show Additive.ofMul (1 : NK.GlobalCFT.IdeleClassGroup K) = 0 from rfl, map_zero]
          exact ofAdd_zero
        map_mul' := by
          intro a b
          rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
            map_add, ofAdd_add] }
  have hΨ_apply : ∀ (n : ℕ) (x : NK.GlobalCFT.IdeleClassGroup K),
      Ψ n x = Multiplicative.ofAdd (Φn n (Additive.ofMul x)) := fun n x => rfl
  have hΨsurj : ∀ n, Function.Surjective (Ψ n) := by
    intro n w
    obtain ⟨x, hx⟩ := hΦnsurj n (Multiplicative.toAdd w)
    refine ⟨Additive.toMul x, ?_⟩
    rw [hΨ_apply]
    show Multiplicative.ofAdd (Φn n (Additive.ofMul (Additive.toMul x))) = w
    rw [show Additive.ofMul (Additive.toMul x) = x from rfl, hx]
    exact ofAdd_toAdd w
  -- ### the tower of open subgroups
  let U : ℕ → Subgroup (NK.GlobalCFT.IdeleClassGroup K) := fun n => (Ψ n).ker
  have hU_apply : ∀ (n : ℕ) (x : NK.GlobalCFT.IdeleClassGroup K),
      (x ∈ U n) ↔ Φn n (Additive.ofMul x) = 0 := by
    intro n x
    show (Ψ n) x = 1 ↔ Φn n (Additive.ofMul x) = 0
    rw [hΨ_apply]
    exact Iff.rfl
  have hker : ∀ n (a : ℤ_[2]),
      a ∈ (Ideal.span {(((2 : ℕ) : ℤ_[2]) ^ n)} : Ideal ℤ_[2]) ↔
        PadicInt.toZModPow (p := 2) n a = 0 := by
    intro n a
    rw [show (Ideal.span {(((2 : ℕ) : ℤ_[2]) ^ n)} : Ideal ℤ_[2])
        = RingHom.ker (PadicInt.toZModPow (p := 2) n) from by rw [PadicInt.ker_toZModPow]]
    exact RingHom.mem_ker
  -- `U n` as a preimage of the open set `((2^n ℤ_2)^r)` under `Φ`
  let S : ℕ → Set (NK.GlobalCFT.IdeleClassGroup K) := fun n =>
    {x | ∀ i, Φ (Additive.ofMul x) i ∈ (Ideal.span {(((2 : ℕ) : ℤ_[2]) ^ n)} : Ideal ℤ_[2])}
  have hU_set : ∀ n, (U n : Set (NK.GlobalCFT.IdeleClassGroup K)) = S n := by
    intro n
    ext x
    change (x ∈ U n) ↔ ∀ i, Φ (Additive.ofMul x) i ∈
      (Ideal.span {(((2 : ℕ) : ℤ_[2]) ^ n)} : Ideal ℤ_[2])
    rw [hU_apply n x, hΦn_apply n (Additive.ofMul x), funext_iff]
    simp only [Pi.zero_apply]
    exact forall_congr' fun i => (hker n (Φ (Additive.ofMul x) i)).symm
  have hSopen : ∀ n, IsOpen (S n) := by
    intro n
    have hsplit : S n = ⋂ i, (fun x : NK.GlobalCFT.IdeleClassGroup K =>
        Φ (Additive.ofMul x) i) ⁻¹'
        ((Ideal.span {(((2 : ℕ) : ℤ_[2]) ^ n)} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
      ext x; simp [S]
    rw [hsplit]
    exact isOpen_iInter_of_finite fun i =>
      (towerRank_isOpen_span_pow 2 n).preimage
        ((continuous_apply i).comp (hΦcont.comp continuous_ofMul))
  refine ⟨U, ?_, ?_, ?_⟩
  · -- the tower is decreasing, by compatibility of the reductions
    intro n x hx
    rw [hU_apply] at hx ⊢
    rw [hΦn_apply] at hx ⊢
    have hx' : ∀ i, PadicInt.toZModPow (p := 2) (n + 1) (Φ (Additive.ofMul x) i) = 0 := by
      intro i
      have := congrFun hx i
      simpa using this
    funext i
    exact towerRank_toZModPow_eq_zero_of_succ n (hx' i)
  · -- the subgroups are open
    intro n
    rw [hU_set n]
    exact hSopen n
  · -- the level isomorphisms
    intro n
    exact ⟨QuotientGroup.quotientKerEquivOfSurjective (Ψ n) (hΨsurj n)⟩

end NK.NUV2.TowerRank
