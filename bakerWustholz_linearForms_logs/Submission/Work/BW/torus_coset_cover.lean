import Mathlib
import Submission.Work.BW.closedSubAux
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covering a set of torus points by finitely many cosets of the kernel of a character lattice

`torChar_ne_zero_of_ne` and `torChar_eq_one_of_mem_span` are the two elementary facts about
monomial characters used below: a character is nonzero on torus points, and the set of points
where a collection of characters is trivial is closed under taking the `ℤ`-span of the
exponents (`charLat` of a singleton).

The main result `torus_coset_cover` shows that a set `K ⊆ (ℂ*)^N` of torus points can be
covered by finitely many cosets of `kerLat (span (range M))` with coset representatives taken
inside `K`, as soon as every row of `M` lies in the saturation of the character lattice of `K`.
The proof picks a finite generating set `s` of `satLat (charLat K)` (submodules of `ℤ^N` are
finitely generated), a common positive multiple `N₀` of the generators with `N₀ • z ∈ charLat K`,
and observes that every `k ∈ K` then has `χ_z(k)^{N₀} = 1` for all generators `z`. Hence the
tuples `(χ_z(k))_z` live in the finite product of the groups of `N₀`-th roots of unity; choosing
one representative in `K` per tuple gives the required finite set.
-/

namespace Work.BW

/-- A monomial character does not vanish on a torus point. -/
lemma torChar_ne_zero_of_ne {N : ℕ} (z : Fin N → ℤ) {y : Fin N → ℂ}
    (hy : ∀ i, y i ≠ 0) : torChar z y ≠ 0 := by
  simp only [torChar]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hy i))

/-- If a monomial character is trivial on the generators `z ∈ s`, it is trivial on the whole
`ℤ`-span of `s`. -/
lemma torChar_eq_one_of_mem_span {N : ℕ} (s : Finset (Fin N → ℤ)) (y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (h : ∀ z ∈ s, torChar z y = 1) :
    ∀ z ∈ Submodule.span ℤ (s : Set (Fin N → ℤ)), torChar z y = 1 := by
  intro z hz
  have hsub : Submodule.span ℤ (s : Set (Fin N → ℤ)) ≤ charLat ({y} : Set (Fin N → ℂ)) := by
    apply Submodule.span_le.mpr
    intro z hz
    refine (mem_charLat_iff).mpr ?_
    intro y' hy' _
    rw [Set.mem_singleton_iff] at hy'
    subst hy'
    exact h z hz
  exact (mem_charLat_iff).mp (hsub hz) y (Set.mem_singleton y) hy

theorem torus_coset_cover {N : ℕ} (K : Set (Fin N → ℂ)) (hK : K ⊆ Tor N)
    (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (hM : ∀ j, M j ∈ satLat (charLat K)) :
    ∃ F : Finset (Fin N → ℂ), (↑F : Set (Fin N → ℂ)) ⊆ K ∧
      ∀ k ∈ K, ∃ f ∈ F, tmul (tInv f) k ∈ kerLat (Submodule.span ℤ (Set.range M)) := by
  classical
  -- Submodules of `ℤ^N` are finitely generated.
  haveI : IsNoetherianRing ℤ := inferInstance
  haveI : IsNoetherian ℤ (Fin N → ℤ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ (Fin N → ℤ)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (satLat (charLat K))
  -- `s` is a finite generating set of `L' = satLat (charLat K)`.
  let ι := {z : Fin N → ℤ // z ∈ s}
  haveI : Fintype ι := Finset.Subtype.fintype s
  have hgen : ∀ z : ι, ∃ m : ℤ, m ≠ 0 ∧ m • z.1 ∈ charLat K := by
    intro z
    have hz : z.1 ∈ satLat (charLat K) := by
      rw [← hs]; exact Submodule.subset_span z.2
    exact hz
  -- Turn the witnessing multiple into a positive natural number.
  have hgen2 : ∀ z : ι, ∃ n : ℕ, n ≠ 0 ∧ (n : ℤ) • z.1 ∈ charLat K := by
    intro z
    obtain ⟨m, hm, hmz⟩ := hgen z
    refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm, ?_⟩
    rcases Int.natAbs_eq m with h | h
    · rw [← h]; exact hmz
    · have h' : ((m.natAbs : ℕ) : ℤ) = -m := by
        have hh := congrArg Neg.neg h
        rw [neg_neg] at hh
        exact hh.symm
      rw [h', neg_smul]
      exact (charLat K).neg_mem hmz
  let mul : ι → ℕ := fun z => Classical.choose (hgen2 z)
  have hmul_ne : ∀ z, mul z ≠ 0 := fun z => (Classical.choose_spec (hgen2 z)).1
  have hmul_mem : ∀ z, (mul z : ℤ) • z.1 ∈ charLat K :=
    fun z => (Classical.choose_spec (hgen2 z)).2
  -- A uniform positive multiple of all generators, again inside `charLat K`.
  let N₀ : ℕ := ∏ z : ι, mul z
  have hN₀_ne : N₀ ≠ 0 := by
    change (∏ z : ι, mul z) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro z _
    exact hmul_ne z
  haveI : NeZero N₀ := ⟨hN₀_ne⟩
  have hN₀_mem : ∀ z : ι, (N₀ : ℤ) • z.1 ∈ charLat K := by
    intro z
    have h := Finset.mul_prod_erase (Finset.univ : Finset ι) (fun w : ι => mul w)
      (Finset.mem_univ z)
    have hN : N₀ = (∏ x ∈ (Finset.univ : Finset ι).erase z, mul x) * mul z := by
      change (∏ x : ι, mul x) = (∏ x ∈ (Finset.univ : Finset ι).erase z, mul x) * mul z
      rw [← h, mul_comm]
    have key : (N₀ : ℤ) • z.1 =
        (((∏ x ∈ (Finset.univ : Finset ι).erase z, mul x : ℕ)) : ℤ) • ((mul z : ℤ) • z.1) := by
      rw [hN, Nat.cast_mul, mul_smul]
    rw [key]
    exact Submodule.smul_mem _ _ (hmul_mem z)
  letI : Fintype (rootsOfUnity N₀ ℂ) := Fintype.ofFinite _
  -- The tuple of characters of a torus point, indexed by the generators.
  let Ψ : K → (ι → rootsOfUnity N₀ ℂ) := fun k z =>
    rootsOfUnity.mkOfPowEq (torChar z.1 k.1) (by
      have h1 : torChar ((N₀ : ℤ) • z.1) k.1 = 1 :=
        (mem_charLat_iff.mp (hN₀_mem z)) k.1 k.2 (fun i => hK k.2 i)
      have h2 : (torChar z.1 k.1) ^ (N₀ : ℤ) = 1 := by
        rw [← torChar_smul (N₀ : ℤ) z.1 (fun i => hK k.2 i), h1]
      rwa [zpow_natCast] at h2)
  -- The (finite) set of tuples realised by points of `K`.
  let T : Finset (ι → rootsOfUnity N₀ ℂ) := Finset.univ.filter (fun t => t ∈ Set.range Ψ)
  have hTmem : ∀ t, t ∈ T ↔ t ∈ Set.range Ψ := by
    intro t; simp [T]
  let rep : (t : {t // t ∈ T}) → K := fun t => Classical.choose ((hTmem t.1).mp t.2)
  have hrep : ∀ t : {t // t ∈ T}, Ψ (rep t) = t.1 :=
    fun t => Classical.choose_spec ((hTmem t.1).mp t.2)
  let F : Finset (Fin N → ℂ) := T.attach.image (fun t => (rep t).1)
  refine ⟨F, ?_, ?_⟩
  · intro y hy
    simp only [F, Finset.coe_image, Finset.coe_attach, Set.mem_image] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact (rep t).2
  · intro k hk
    let k' : K := ⟨k, hk⟩
    have hmem : Ψ k' ∈ T := (hTmem _).mpr ⟨k', rfl⟩
    let t : {t // t ∈ T} := ⟨Ψ k', hmem⟩
    have hΨt : Ψ (rep t) = Ψ k' := by rw [hrep t]
    refine ⟨(rep t).1, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨t, Finset.mem_attach T t, rfl⟩
    · refine ⟨fun i => mul_ne_zero (inv_ne_zero ?_) (hK hk i), ?_⟩
      · exact hK (rep t).2 i
      · intro w hw
        have hgen1 : ∀ z : ι, torChar z.1 (tmul (tInv (rep t).1) k) = 1 := by
          intro z
          have hcoord : ((Ψ (rep t) z : ℂˣ) : ℂ) = ((Ψ k' z : ℂˣ) : ℂ) := by
            rw [hΨt]
          simp only [Ψ, rootsOfUnity.coe_mkOfPowEq] at hcoord
          rw [torChar_tmul, torChar_tInv, hcoord, inv_mul_cancel₀]
          exact torChar_ne_zero_of_ne z.1 (fun i => hK hk i)
        have hw' : w ∈ Submodule.span ℤ (s : Set (Fin N → ℤ)) := by
          rw [hs]
          exact Submodule.span_le.mpr (fun x hx => by
            obtain ⟨j, rfl⟩ := hx; exact hM j) hw
        exact torChar_eq_one_of_mem_span s (tmul (tInv (rep t).1) k)
          (fun i => mul_ne_zero (inv_ne_zero (hK (rep t).2 i)) (hK hk i))
          (fun z hz => hgen1 ⟨z, hz⟩) w hw'

end Work.BW
