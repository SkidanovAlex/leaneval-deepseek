import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.StemsB.fg_abelian_decomposition
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Work.Pi6.EMZ.groupZModTwo`

A finitely generated abelian group `G` satisfying

* `G ⧸ 2·G` has at most two elements,
* `G` is `p`-divisible and has no `p`-torsion for every odd prime `p`,
* `G` contains an element `a` of order `2` which is *not* a double,

is isomorphic to `ℤ/2`.

This is the group-theoretic step of the EMZ area (`REFS/NOTES_LEAD_PI6.md` §7): a cyclic
2-group `C` with an element `a` such that `2a = 0` and `a ∉ 2C` is `ℤ/2`.

The argument is in four steps, each an independent lemma:

1. `fgDivisibleFinite`: a finitely generated `ℤ`-module which is `p`-divisible for *one*
   prime `p` is finite.  Hence `G` is finite, using `hdiv` at `p = 3`.
2. `finiteNoOddTorsionTwoPow`: a finite abelian group without odd torsion is a 2-group,
   elementwise.  Used for the quotient `G ⧸ ℤa`.
3. `G = 2·G + ℤ·a`: from `|G ⧸ 2·G| ≤ 2` and `a ∉ 2·G` the quotient `G ⧸ 2·G` is exactly
   `{0, a}` (cardinality argument on the two-element set `{0, ā}`).
4. `G ⧸ ℤa` is a finite 2-group with `H = 2·H`; as `2` acts bijectively on a finite type,
   `H = 0`, so `G = ℤa` and `cyclicOrderTwoLinearEquiv` finishes.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Pi6.EMZ

noncomputable section

/-- **A finitely generated `ℤ`-module which is `p`-divisible for a prime `p` is finite.**

Via the structure theorem `Work.StemsB.fg_abelian_decomposition`, write `M ≃+ ℤ^r × F` with `F`
finite.  `p`-divisibility forces the class of `(1 : ℤ)` in `ℤ^r / p·ℤ^r` to vanish, which is
impossible for `r ≥ 1` since `p ≥ 2`; hence `r = 0` and `M ≅ F` is finite. -/
theorem fgDivisibleFinite (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (p : ℕ)
    (hp : p.Prime) (h : Subsingleton (M ⧸ pH p M)) : Finite M := by
  classical
  obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition M
  haveI := hFfin
  have hdiv : ∀ x : M, ∃ y : M, p • y = x := subsingleton_quot_pH_iff.mp h
  have hr : r = 0 := by
    by_contra hr
    have hpos : 0 < r := Nat.pos_of_ne_zero hr
    let i : Fin r := ⟨0, hpos⟩
    let z : (Fin r → ℤ) × F := (Pi.single i 1, 0)
    obtain ⟨y, hy⟩ := hdiv (e.symm z)
    have h1 : z = p • (e y) := by
      rw [← map_nsmul, hy, AddEquiv.apply_symm_apply]
    have h2 : (1 : ℤ) = (p : ℤ) * ((e y).1 i) := by
      have := congrFun (congrArg Prod.fst h1) i
      simp only [z, Prod.smul_fst, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul] at this
      exact this
    have hdvd : p ∣ 1 := by
      have := congrArg Int.natAbs h2
      simp only [Int.natAbs_one, Int.natAbs_mul, Int.natAbs_natCast] at this
      exact ⟨((e y).1 i).natAbs, this⟩
    rw [Nat.dvd_one] at hdvd
    have hp2 := hp.two_le
    omega
  rw [hr] at e
  exact Finite.of_equiv ((Fin 0 → ℤ) × F) e.symm.toEquiv

/-- **A finite abelian group with no odd torsion is a 2-group, elementwise.**

If an odd prime `p` divided the order of `x`, then `(addOrderOf x / p) • x` would be a nonzero
element killed by `p`, contradicting `Subsingleton (torsP p G)`.  Hence the order of `x` is a
power of `2`. -/
theorem finiteNoOddTorsionTwoPow (G : Type) [AddCommGroup G] [Finite G]
    (htor : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (torsP p G)) :
    ∀ x : G, ∃ n : ℕ, (2 : ℕ) ^ n • x = 0 := by
  -- an auxiliary arithmetic fact: a positive integer all of whose prime divisors are `2`
  -- is a power of `2`
  have key : ∀ n : ℕ, 0 < n → (∀ p : ℕ, p.Prime → p ∣ n → p = 2) → ∃ k, n = 2 ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hpr
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
        have hp_eq : p = 2 := hpr p hp hpdvd
        subst hp_eq
        obtain ⟨m, hm⟩ := hpdvd
        have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        have hpr' : ∀ q : ℕ, q.Prime → q ∣ m → q = 2 := by
          intro q hq hqdvd
          exact hpr q hq (hqdvd.trans ⟨2, by rw [hm, mul_comm]⟩)
        obtain ⟨k, hk⟩ := ih m hmlt hmpos hpr'
        exact ⟨k + 1, by rw [hm, hk, pow_succ, mul_comm]⟩
  intro x
  have hfin : IsOfFinAddOrder x := isOfFinAddOrder_of_finite x
  have hrpos : 0 < addOrderOf x := addOrderOf_pos_iff.mpr hfin
  have hpr : ∀ p : ℕ, p.Prime → p ∣ addOrderOf x → p = 2 := by
    intro p hp hpdvd
    by_contra hp2
    haveI : Subsingleton (torsP p G) := htor p hp hp2
    have hp_mul : p * (addOrderOf x / p) = addOrderOf x := Nat.mul_div_cancel' hpdvd
    have hy0 : p • ((addOrderOf x / p) • x) = 0 := by
      rw [← nsmul_left_comm, ← mul_nsmul, hp_mul, addOrderOf_nsmul_eq_zero]
    have hple : p ≤ addOrderOf x := Nat.le_of_dvd hrpos hpdvd
    have hpos' : 0 < addOrderOf x / p := Nat.div_pos hple hp.pos
    have hyne : (addOrderOf x / p) • x ≠ 0 := by
      intro hzero
      have hdvd' : addOrderOf x ∣ addOrderOf x / p :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
      have hlt : addOrderOf x / p < addOrderOf x := Nat.div_lt_self hrpos hp.one_lt
      have hle' : addOrderOf x ≤ addOrderOf x / p := Nat.le_of_dvd hpos' hdvd'
      omega
    have hmem : (addOrderOf x / p) • x ∈ torsP p G := mem_torsP'.mpr hy0
    have := Subsingleton.elim (⟨(addOrderOf x / p) • x, hmem⟩ : torsP p G) ⟨0, by simp⟩
    exact hyne (congrArg Subtype.val this)
  obtain ⟨k, hk⟩ := key (addOrderOf x) hrpos hpr
  exact ⟨k, by rw [← hk]; exact addOrderOf_nsmul_eq_zero x⟩

/-- **A group generated by an element of order two is `ℤ/2`.**

Under `ℤ →ₗ[ℤ] G`, `n ↦ n • a`, the kernel is `2ℤ` (because `addOrderOf a = 2`) and the map is
surjective (because `a` generates); the first isomorphism theorem plus
`ℤ ⧸ 2ℤ ≅ ZMod 2` gives the claim. -/
theorem cyclicOrderTwoLinearEquiv (G : Type) [AddCommGroup G] (a : G)
    (ha2 : 2 • a = 0) (ha0 : a ≠ 0) (hgen : AddSubgroup.closure ({a} : Set G) = ⊤) :
    Nonempty (G ≃ₗ[ℤ] ZMod 2) := by
  classical
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ G a) := by
    intro x
    have hx : x ∈ AddSubgroup.closure ({a} : Set G) := hgen ▸ AddSubgroup.mem_top x
    obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hx
    exact ⟨n, by rw [LinearMap.toSpanSingleton_apply]; exact hn⟩
  have hne1 : addOrderOf a ≠ 1 := by
    intro h
    have := addOrderOf_nsmul_eq_zero a
    rw [h, one_nsmul] at this
    exact ha0 this
  have haord : addOrderOf a = 2 := by
    have h1 : addOrderOf a ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr ha2
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd h hne1
    · exact h
  have hker : LinearMap.ker (LinearMap.toSpanSingleton ℤ G a) = Ideal.span ({2} : Set ℤ) := by
    ext n
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton,
      ← addOrderOf_dvd_iff_zsmul_eq_zero, haord]
    norm_num
  have h1 : (ℤ ⧸ LinearMap.ker (LinearMap.toSpanSingleton ℤ G a)) ≃ₗ[ℤ] G :=
    (LinearMap.toSpanSingleton ℤ G a).quotKerEquivOfSurjective hsurj
  have h2 : (ℤ ⧸ LinearMap.ker (LinearMap.toSpanSingleton ℤ G a)) ≃ₗ[ℤ]
      (ℤ ⧸ Ideal.span ({2} : Set ℤ)) :=
    Submodule.quotEquivOfEq _ _ hker
  have h3 : (ℤ ⧸ Ideal.span ({2} : Set ℤ)) ≃ₗ[ℤ] ZMod 2 :=
    (Int.quotientSpanEquivZMod 2).toAddEquiv.toIntLinearEquiv
  exact ⟨h1.symm.trans (h2.trans h3)⟩

/-- Suppose `G` is a finitely generated abelian group such that

* `G ⧸ 2·G` has at most two elements,
* `G` is `p`-divisible and has no `p`-torsion for all odd primes `p`,
* there is `a` with `2·a = 0` and `a ∉ 2·G`.

Then `G ≅ ℤ/2`. -/
theorem groupZModTwo (G : Type) [AddCommGroup G] [Module.Finite ℤ G]
    (h2 : Nat.card (G ⧸ Work.Pi6.EMZ.pH 2 G) ≤ 2)
    (hdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (G ⧸ Work.Pi6.EMZ.pH p G))
    (htor : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (Work.Pi6.EMZ.torsP p G))
    (ha : ∃ a : G, 2 • a = 0 ∧ ∀ b : G, 2 • b ≠ a) :
    Nonempty (G ≃ₗ[ℤ] ZMod 2) := by
  classical
  obtain ⟨a, ha2, hamin⟩ := ha
  -- Step 1: `G` is finite (`3`-divisibility).
  haveI hGfin : Finite G :=
    fgDivisibleFinite G 3 (by norm_num) (hdiv 3 (by norm_num) (by norm_num))
  have ha0 : a ≠ 0 := by
    intro h0
    exact hamin 0 (by simp [h0])
  have hane : a ∉ pH 2 G := by
    intro hmem
    obtain ⟨y, hy⟩ := mem_pH'.mp hmem
    exact hamin y hy
  have hne : ((a : G ⧸ pH 2 G)) ≠ 0 := fun hq => hane ((QuotientAddGroup.eq_zero_iff a).mp hq)
  -- Step 2: `G ⧸ 2·G = {0, a}`, since it has at most two elements and contains `a ≠ 0`.
  have hS : ({0, (a : G ⧸ pH 2 G)} : Set (G ⧸ pH 2 G)) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, Set.ncard_pair hne.symm]
    exact h2
  -- Step 3: `G = 2·G + ℤ·a`.
  have hcover : ∀ x : G, x ∈ pH 2 G ∨ (x - a) ∈ pH 2 G := by
    intro x
    have hx : (x : G ⧸ pH 2 G) ∈ ({0, (a : G ⧸ pH 2 G)} : Set (G ⧸ pH 2 G)) := by
      rw [hS]; exact Set.mem_univ _
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · exact Or.inl ((QuotientAddGroup.eq_zero_iff x).mp hx)
    · exact Or.inr ((QuotientAddGroup.eq_iff_sub_mem).mp hx)
  have hgen : ∀ x : G, ∃ (y : G) (n : ℤ), 2 • y + n • a = x := by
    intro x
    rcases hcover x with h | h
    · obtain ⟨y, hy⟩ := mem_pH'.mp h
      exact ⟨y, 0, by rw [zero_zsmul, add_zero]; exact hy⟩
    · obtain ⟨y, hy⟩ := mem_pH'.mp h
      refine ⟨y, 1, ?_⟩
      rw [one_zsmul, hy]
      abel
  -- Step 4: `H := G ⧸ ℤa` is `2`-divisible and every element of `H` has `2`-power order;
  -- as `H` is finite, this forces `H = 0`.
  set K : AddSubgroup G := AddSubgroup.closure ({a} : Set G) with hKdef
  have haK : (a : G ⧸ K) = 0 :=
    (QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.subset_closure (Set.mem_singleton a))
  have hK2 : ∀ z : G ⧸ K, ∃ z' : G ⧸ K, 2 • z' = z := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨y, n, hy⟩ := hgen x
    refine ⟨(y : G ⧸ K), ?_⟩
    have hq : ((x : G ⧸ K)) = 2 • ((y : G ⧸ K)) := by
      conv_lhs => rw [← hy]
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, QuotientAddGroup.mk_zsmul,
        haK, smul_zero, add_zero]
    exact hq.symm
  have hKpow : ∀ z : G ⧸ K, ∃ n : ℕ, (2 : ℕ) ^ n • z = 0 := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨n, hn⟩ := finiteNoOddTorsionTwoPow G htor x
    refine ⟨n, ?_⟩
    have hmk : (QuotientAddGroup.mk' K) (2 ^ n • x) = 2 ^ n • (QuotientAddGroup.mk' K x) :=
      map_nsmul (QuotientAddGroup.mk' K) (2 ^ n) x
    rw [hn, map_zero] at hmk
    simpa [QuotientAddGroup.mk'_apply] using hmk.symm
  have hKsub : Subsingleton (G ⧸ K) := by
    refine ⟨fun p q => ?_⟩
    have hzero : ∀ z : G ⧸ K, z = 0 := by
      have hinj : Function.Injective (fun z : G ⧸ K => 2 • z) :=
        Finite.injective_iff_surjective.mpr (fun z => hK2 z)
      have hmain : ∀ n : ℕ, ∀ z : G ⧸ K, (2 : ℕ) ^ n • z = 0 → z = 0 := by
        intro n
        induction n with
        | zero => intro z hz; simpa using hz
        | succ n ih =>
          intro z hz
          have hz' : (2 : ℕ) ^ n • (2 • z) = 0 := by
            rw [nsmul_left_comm]
            rw [← hz, pow_succ, mul_nsmul]
          have h2z : 2 • z = 0 := ih (2 • z) hz'
          exact hinj (by simp [h2z])
      intro z
      obtain ⟨n, hn⟩ := hKpow z
      exact hmain n z hn
    rw [hzero p, hzero q]
  have hKtop : K = ⊤ := by
    rw [AddSubgroup.eq_top_iff' K]
    intro x
    exact (QuotientAddGroup.eq_zero_iff x).mp (hKsub.elim (x : G ⧸ K) 0)
  exact cyclicOrderTwoLinearEquiv G a ha2 ha0 hKtop

end

end Work.Pi6.EMZ
