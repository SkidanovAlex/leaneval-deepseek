import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.irr_degree_dvd_card
import Submission.Work.CharCore.column_orthogonality_not_conj
import Submission.Work.CharCore.norm_char_eq_iff_isScalar
import Submission.Work.CharCore.dvd_of_isIntegral_rat
import Submission.Work.CharCore.avg_rootsOfUnity_integral

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Burnside's `p^a q^b` theorem (core case)

No finite non-abelian simple group has order `p ^ a * q ^ b` for primes `p, q`.

The proof is the classical character-theoretic one (Huppert, *Endliche Gruppen I*, V.7.2 + V.7.3):

* pick a Sylow `p`-subgroup `S` and `1 ≠ x ∈ Z(S)`; then `x ∉ Z(G)`, so the conjugacy class of
  `x` has size `q ^ d` with `d > 0` (it divides `[G : S] = q ^ b`);
* column orthogonality `∑_{χ ∈ Irr G} χ 1 * χ x = 0` plus integrality of the `χ x` shows that some
  non-principal `χ` has `q ∤ χ 1` and `χ x ≠ 0`;
* for that `χ`, the class-sum central character gives integrality of `q ^ d * χ x / χ 1`, and since
  `gcd(q ^ d, χ 1) = 1` Bézout makes `χ x / χ 1` an algebraic integer; as it is an average of
  roots of unity, Huppert V.7.1 gives `‖χ x‖ = χ 1`;
* the equality case `norm_char_eq_iff_isScalar` makes `ρ x` a scalar matrix, so `x` is central —
  contradiction with `x ≠ 1` in a group with trivial centre.

All the algebraic-integrality and character-theory inputs are the ones available in
`Work.CharCore`.
-/

noncomputable section

open Classical

namespace Work.CharCore

/-- A finite simple group that is a `p`-group is commutative (its centre is a nontrivial normal
subgroup). -/
theorem isMulCommutative_of_isSimpleGroup_of_isPGroup {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {p : ℕ} [Fact p.Prime] (h : IsPGroup p G) : IsMulCommutative G := by
  have hnt : Nontrivial (Subgroup.center G) := h.center_nontrivial
  have hne : Subgroup.center G ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hnt
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ (Subgroup.center G) inferInstance with hb | ht
  · exact absurd hb hne
  · exact Subgroup.center_eq_top_iff.mp ht

/-- The size of the conjugacy class of `x` equals the index of its centralizer. -/
theorem nat_card_conjClass_carrier_eq_index_centralizer {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (Subgroup.centralizer ({x} : Set G)).index := by
  have h2 : (Subgroup.centralizer ({x} : Set G)).index =
      (MulAction.stabilizer (ConjAct G) x).index := by
    rw [Subgroup.centralizer_eq_comap_stabilizer x]
    exact Subgroup.index_comap_of_surjective (G := ConjAct G) (G' := G)
      (H := MulAction.stabilizer (ConjAct G) x) (f := ConjAct.toConjAct.toMonoidHom)
      ConjAct.toConjAct.surjective
  have h1 : Nat.card (ConjClasses.mk x).carrier =
      (MulAction.stabilizer (ConjAct G) x).index := by
    rw [← ConjAct.orbit_eq_carrier_conjClasses x, Nat.card_coe_set_eq]
    exact (MulAction.index_stabilizer (ConjAct G) x).symm
  rw [h2, ← h1]

/-- **Group-theoretic input.**  A finite non-abelian simple group of order `p ^ a * q ^ b`
(`p, q` primes) has an element `x ≠ 1` whose conjugacy class has size `q ^ d` with `d > 0`. -/
theorem exists_conjClass_card_prime_pow {G : Type*} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ¬ IsMulCommutative G)
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hcard : Nat.card G = p ^ a * q ^ b) :
    ∃ (x : G) (d : ℕ), x ≠ 1 ∧ 0 < d ∧ Nat.card (ConjClasses.mk x).carrier = q ^ d := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hcenter : Subgroup.center G = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnab
  by_cases ha : a = 0
  · exfalso
    subst ha
    rw [pow_zero, one_mul] at hcard
    exact hnab (isMulCommutative_of_isSimpleGroup_of_isPGroup (IsPGroup.of_card hcard))
  by_cases hb : b = 0
  · exfalso
    subst hb
    rw [pow_zero, mul_one] at hcard
    exact hnab (isMulCommutative_of_isSimpleGroup_of_isPGroup (IsPGroup.of_card hcard))
  by_cases hpq : p = q
  · exfalso
    subst hpq
    rw [← pow_add] at hcard
    exact hnab (isMulCommutative_of_isSimpleGroup_of_isPGroup (IsPGroup.of_card hcard))
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  have hdiv : p ^ a ∣ Nat.card G := by rw [hcard]; exact dvd_mul_right _ _
  obtain ⟨P, hPcard⟩ := Sylow.exists_subgroup_card_pow_prime p hdiv
  haveI hPpg : IsPGroup p P := IsPGroup.of_card hPcard
  haveI hPnt : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPcard]
    exact one_lt_pow₀ hp.one_lt (Nat.pos_iff_ne_zero.mp hapos)
  have hZnt : Nontrivial (Subgroup.center P) := IsPGroup.center_nontrivial hPpg
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center P)
  set x : G := ((z : P) : G) with hxdef
  have hx1 : x ≠ 1 := by
    intro h
    apply hz1
    exact Subtype.ext (Subtype.ext h)
  have hPle : P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hz := Subgroup.mem_center_iff.mp z.2 (⟨k, hk⟩ : P)
    have hzG : k * ((z : P) : G) = ((z : P) : G) * k := by
      have := congrArg (fun w : P => (w : G)) hz
      simpa using this
    exact hzG.symm
  have hPind : P.index = q ^ b := by
    have h := Subgroup.card_mul_index P
    rw [hPcard, hcard] at h
    exact Nat.mul_left_cancel (pow_pos hp.pos a) h
  have hdvd : Nat.card (ConjClasses.mk x).carrier ∣ q ^ b := by
    rw [nat_card_conjClass_carrier_eq_index_centralizer x, ← hPind]
    exact Subgroup.index_dvd_of_le hPle
  obtain ⟨d, hdb, hclass⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  have hxnotcenter : x ∉ Subgroup.center G := by
    rw [hcenter]; intro h; exact hx1 (Subgroup.mem_bot.mp h)
  have hnetop : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
    intro h
    apply hxnotcenter
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({x} : Set G) := h ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
  have hlt : 1 < Nat.card (ConjClasses.mk x).carrier := by
    rw [nat_card_conjClass_carrier_eq_index_centralizer]
    exact Subgroup.one_lt_index_of_ne_top hnetop
  refine ⟨x, d, hx1, ?_, hclass⟩
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0, pow_zero] at hclass
    omega
  · exact hdpos

/-- **Isaacs, Theorem 3.7.**  If `χ ∈ Irr G`, `x : G` and `gcd(|cl x|, χ 1) = 1`, then
`χ x / χ 1` is an algebraic integer.

The class-sum central character `ω` of the conjugacy class of `x` is integral over `ℤ` and
satisfies `ω * χ 1 = |cl x| * χ x`; since `|cl x|` and `χ 1` are coprime, Bézout expresses
`χ x / χ 1` as an integral combination of `ω` and `χ x` (the latter also integral). -/
theorem isIntegral_char_div_irrDeg {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (x : G)
    (hcop : Nat.Coprime (Nat.card (ConjClasses.mk x).carrier) (irrDeg χ)) :
    IsIntegral ℤ (χ x / (irrDeg χ : ℂ)) := by
  classical
  obtain ⟨N, hNmem, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  have hN : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hNmem
  obtain ⟨a, b, hab⟩ := hcop.isCoprime
  set C : ConjClasses G := ConjClasses.mk x with hC
  have hxmem : x ∈ C.carrier := ConjClasses.mem_carrier_mk
  set ω : ℂ := centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ with hωdef
  have hω : IsIntegral ℤ ω := isIntegral_centralChar_classSum N hN C
  have hdeg : Module.finrank ℂ N = irrDeg χ := (irrDeg_eq_finrank hχ hNmem hNχ).symm
  have hrep : (submoduleRep N).character (rep C) = χ x := by
    rw [hNχ]
    exact ((IsClassFun.eq_rep (isClassFun_of_mem_Irr hχ) hxmem)).symm
  have hkey : ω * (irrDeg χ : ℂ) = (Nat.card (ConjClasses.mk x).carrier : ℂ) * χ x := by
    have h := centralChar_classSum_mul_finrank N hN C
    rw [hdeg, hrep, ← Nat.card_eq_fintype_card, hC] at h
    exact h
  have hχx : IsIntegral ℤ (χ x) := by
    have := Representation.isIntegral_character (submoduleRep N) x
    rwa [hNχ] at this
  have hne : (irrDeg χ : ℂ) ≠ 0 := irrDeg_ne_zero hχ
  have hcast : (a : ℂ) * (Nat.card (ConjClasses.mk x).carrier : ℂ)
      + (b : ℂ) * (irrDeg χ : ℂ) = 1 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hab
    push_cast at this
    simpa using this
  have hval : χ x / (irrDeg χ : ℂ) = (a : ℂ) * ω + (b : ℂ) * χ x := by
    rw [div_eq_iff hne]
    have h1 : ((a : ℂ) * ω + (b : ℂ) * χ x) * (irrDeg χ : ℂ) = χ x := by
      calc ((a : ℂ) * ω + (b : ℂ) * χ x) * (irrDeg χ : ℂ)
          = (a : ℂ) * (ω * (irrDeg χ : ℂ)) + (b : ℂ) * (χ x * (irrDeg χ : ℂ)) := by ring
        _ = (a : ℂ) * ((Nat.card (ConjClasses.mk x).carrier : ℂ) * χ x)
              + (b : ℂ) * (χ x * (irrDeg χ : ℂ)) := by rw [hkey]
        _ = ((a : ℂ) * (Nat.card (ConjClasses.mk x).carrier : ℂ)
              + (b : ℂ) * (irrDeg χ : ℂ)) * χ x := by ring
        _ = 1 * χ x := by rw [hcast]
        _ = χ x := by ring
    exact h1.symm
  rw [hval]
  exact (IsIntegral.mul (isIntegral_intCast a) hω).add
    (IsIntegral.mul (isIntegral_intCast b) hχx)

/-- For `x ≠ 1` in a finite group and a prime `q`, there is a non-principal irreducible
character `χ` with `q ∤ χ 1` and `χ x ≠ 0`.

Column orthogonality gives `∑_{χ ∈ Irr G} χ 1 * χ x = 0`.  If no such `χ` existed, then
`-1 = ∑_{χ ≠ principal, χ x ≠ 0} χ 1 * χ x`, and dividing by the prime `q` would exhibit
`-1 / q` as an integral linear combination of the algebraic integers `χ x`, an absurdity. -/
theorem exists_irr_not_dvd_deg_char_ne_zero {G : Type*} [Group G] [Fintype G] {x : G}
    (hx : x ≠ 1) {q : ℕ} (hq : q.Prime) :
    ∃ χ ∈ Irr G,
      χ ≠ (fun _ : G => (1 : ℂ)) ∧ ¬ q ∣ irrDeg χ ∧ χ x ≠ 0 := by
  classical
  by_contra hgood
  have hq_dvd : ∀ χ ∈ Irr G, χ ≠ (fun _ : G => (1 : ℂ)) → χ x ≠ 0 → q ∣ irrDeg χ := by
    intro χ hχ hne hval
    by_contra hnd
    exact hgood ⟨χ, hχ, hne, hnd, hval⟩
  have hcharInt : ∀ χ ∈ Irr G, IsIntegral ℤ (χ x) := by
    intro χ hχ
    obtain ⟨N, _, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
    have := Representation.isIntegral_character (submoduleRep N) x
    rwa [hNχ] at this
  have hnc : ¬ IsConj x 1 := fun h => hx (isConj_one_left.mp h)
  have hS : ∑ χ ∈ Irr G, χ 1 * χ x = 0 := by
    have hcol := column_orthogonality_not_conj (G := G) (g := x) (h := 1) hnc
    rw [← hcol]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [star_Irr χ hχ 1, inv_one]
    ring
  have hP : (fun _ : G => (1 : ℂ)) ∈ Irr G := principalChar_mem_Irr
  have hT : ∑ χ ∈ (Irr G).erase (fun _ : G => (1 : ℂ)), χ 1 * χ x = -1 := by
    have herase := Finset.sum_erase_add (Irr G) (fun χ => χ 1 * χ x) hP
    rw [hS] at herase
    have h2 : (∑ χ ∈ (Irr G).erase (fun _ : G => (1 : ℂ)), χ 1 * χ x) + 1 = 0 := by
      simpa using herase
    exact add_eq_zero_iff_eq_neg.mp h2
  have hkey : (-1 : ℂ) / q
      = ∑ χ ∈ (Irr G).erase (fun _ : G => (1 : ℂ)), ((irrDeg χ : ℂ) / q) * χ x := by
    rw [← hT, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [irrDeg_spec (Finset.mem_of_mem_erase hχ)]
    ring
  have hintC : IsIntegral ℤ ((-1 : ℂ) / q) := by
    rw [hkey]
    refine IsIntegral.sum _ fun χ hχ => ?_
    by_cases hval : χ x = 0
    · rw [hval, mul_zero]; exact isIntegral_zero
    · have hχmem : χ ∈ Irr G := Finset.mem_of_mem_erase hχ
      have hne : χ ≠ (fun _ : G => (1 : ℂ)) := (Finset.mem_erase.mp hχ).1
      have hdvd : q ∣ irrDeg χ := hq_dvd χ hχmem hne hval
      have hdiv : (irrDeg χ : ℂ) / q = ((irrDeg χ / q : ℕ) : ℂ) := by
        rw [Nat.cast_div hdvd (Nat.cast_ne_zero.mpr hq.ne_zero)]
      rw [hdiv]
      exact (isIntegral_natCast (irrDeg χ / q)).mul (hcharInt χ hχmem)
  have hintQ : IsIntegral ℤ ((-1 : ℚ) / q) := by
    rw [← isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ) (x := (-1 : ℚ) / q)]
    convert hintC using 1
    push_cast
    ring
  have h1 : IsIntegral ℤ ((1 : ℚ) / q) := by
    have := hintQ.neg
    convert this using 1
    ring
  exact hq.not_dvd_one (dvd_of_isIntegral_rat hq.pos h1)

/-- **The contradiction from a non-principal `χ` with `q ∤ χ 1` and `χ x ≠ 0`, where `x` has
class size `q ^ d` (`d > 0`)**, in a simple group.

`χ x / χ 1` is an algebraic integer (Isaacs 3.7) and an average of `χ 1` roots of unity, so
Huppert V.7.1 gives `‖χ x‖ = χ 1`; then `norm_char_eq_iff_isScalar` makes `ρ x` a scalar matrix.
Since `χ ≠ 1` and `G` is simple the representation `ρ` is faithful, so `x` is central, forcing
`Z(G) = ⊤`, `G` abelian, and the class of `x` a singleton — contradicting `q ^ d ≥ 2`. -/
theorem false_of_prime_pow_class_chi {G : Type*} [Group G] [Fintype G]
    (hsimple : IsSimpleGroup G) {x : G} (hx : x ≠ 1) {q d : ℕ} (hq : q.Prime) (hd : 0 < d)
    (hclass : Nat.card (ConjClasses.mk x).carrier = q ^ d)
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (hne : χ ≠ (fun _ : G => (1 : ℂ)))
    (hqdvd : ¬ q ∣ irrDeg χ) (hval : χ x ≠ 0) : False := by
  classical
  obtain ⟨N, hNmem, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  have hN : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hNmem
  haveI hIrr : (submoduleRep N).IsIrreducible := isIrreducible_submoduleRep N hN
  have hdeg : Module.finrank ℂ N = irrDeg χ := (irrDeg_eq_finrank hχ hNmem hNχ).symm
  -- the ring of the class-sum argument
  have hcop : Nat.Coprime (Nat.card (ConjClasses.mk x).carrier) (irrDeg χ) := by
    rw [hclass]
    exact (hq.coprime_iff_not_dvd.mpr hqdvd).pow_left d
  have hint : IsIntegral ℤ (χ x / (irrDeg χ : ℂ)) := isIntegral_char_div_irrDeg hχ x hcop
  -- `χ x / χ 1` is an average of `orderOf x`-th roots of unity
  have hsplits : ((submoduleRep N) x).charpoly.Splits := IsAlgClosed.splits _
  have htr : (submoduleRep N).character x = ((submoduleRep N) x).charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  have hroot : ∀ y ∈ ((submoduleRep N) x).charpoly.roots, y ^ orderOf x = 1 := by
    intro y hy
    have hev : Module.End.HasEigenvalue ((submoduleRep N) x) y :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ y).2 (Polynomial.isRoot_of_mem_roots hy)
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hev
    have hpowmap : ((submoduleRep N) x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have key : y ^ orderOf x • v = v := by
      rw [← Module.End.HasEigenvector.pow_apply hv (orderOf x), hpowmap, Module.End.one_apply]
    exact smul_left_injective ℂ hv.2 (by simpa using key)
  have hcard : ((submoduleRep N) x).charpoly.roots.card = irrDeg χ := by
    have h1 := hsplits.natDegree_eq_card_roots
    have h2 := LinearMap.charpoly_natDegree ((submoduleRep N) x)
    rw [← h1, h2]
    exact hdeg
  have hssum : ((submoduleRep N) x).charpoly.roots.sum
      = (irrDeg χ : ℂ) * (χ x / (irrDeg χ : ℂ)) := by
    rw [← htr, hNχ, mul_div_cancel₀ _ (irrDeg_ne_zero hχ)]
  have hL1 := avg_rootsOfUnity_integral (irrDeg_pos hχ) (orderOf_pos x) hint
    ⟨((submoduleRep N) x).charpoly.roots, hcard, hroot, hssum⟩
  have hz0 : χ x / (irrDeg χ : ℂ) ≠ 0 := div_ne_zero hval (irrDeg_ne_zero hχ)
  have hnorm1 : ‖χ x / (irrDeg χ : ℂ)‖ = 1 := hL1.resolve_left hz0
  have hnormχ : ‖χ x‖ = (irrDeg χ : ℝ) := by
    rw [norm_div, Complex.norm_natCast] at hnorm1
    rwa [div_eq_one_iff_eq (by exact_mod_cast (irrDeg_pos hχ).ne')] at hnorm1
  have hchi : ‖(submoduleRep N).character x‖ = (irrDeg (submoduleRep N).character : ℝ) := by
    rw [hNχ]
    exact hnormχ
  obtain ⟨c, _hc1, hcs⟩ := (norm_char_eq_iff_isScalar (submoduleRep N) hIrr x).mp hchi
  -- the representation is faithful, because otherwise its character would be trivial
  have hinj : Function.Injective (submoduleRep N) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple (MonoidHom.ker (submoduleRep N))
      (MonoidHom.normal_ker _) with h | h
    · exact h
    · exfalso
      have htriv : ∀ g : G, χ g = (irrDeg χ : ℂ) := by
        intro g
        have hg : (submoduleRep N) g = 1 := by
          have : g ∈ MonoidHom.ker (submoduleRep N) := by rw [h]; exact Subgroup.mem_top g
          exact MonoidHom.mem_ker.mp this
        have ht : (submoduleRep N).character g = (irrDeg χ : ℂ) := by
          rw [Representation.character, hg, LinearMap.trace_one, hdeg]
        exact hNχ ▸ ht
      have hnorm2 : (irrDeg χ : ℂ) ^ 2 = 1 := by
        have h1 : cfInner χ χ = 1 := cfInner_self_mem_Irr hχ
        rw [cfInner_apply] at h1
        have hsum : ∑ g : G, χ g * starRingEnd ℂ (χ g)
            = (Fintype.card G : ℂ) * (irrDeg χ : ℂ) ^ 2 := by
          calc ∑ g : G, χ g * starRingEnd ℂ (χ g)
              = ∑ _g : G, (irrDeg χ : ℂ) ^ 2 := by
                refine Finset.sum_congr rfl fun g _ => ?_
                rw [htriv g]
                simp only [map_natCast]
                ring
            _ = (Fintype.card G : ℂ) * (irrDeg χ : ℂ) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [hsum] at h1
        have hc : (Fintype.card G : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        have h2 := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z) h1
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h2
        exact mul_left_cancel₀ hc h2
      have h3 : (irrDeg χ : ℂ) = 1 := by
        rcases sq_eq_one_iff.mp hnorm2 with h | h
        · exact h
        · exfalso
          have h4 : (irrDeg χ : ℝ) = -1 := by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_one]
            exact h
          have := irrDeg_pos' hχ
          linarith
      apply hne
      funext g
      show χ g = 1
      rw [htriv g, h3]
  -- `x` is central
  have hxcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hinj
    have : (submoduleRep N) y * (submoduleRep N) x
        = (submoduleRep N) x * (submoduleRep N) y := by
      rw [hcs, ← Algebra.algebraMap_eq_smul_one]
      exact (Algebra.commute_algebraMap_right c ((submoduleRep N) y)).eq
    rw [map_mul, map_mul]
    exact this
  -- hence `G` is commutative and the class of `x` is a singleton
  have hZtop : Subgroup.center G = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple (Subgroup.center G) inferInstance with h | h
    · exfalso
      rw [h] at hxcenter
      exact hx (Subgroup.mem_bot.mp hxcenter)
    · exact h
  have hcommG : IsMulCommutative G := Subgroup.center_eq_top_iff.mp hZtop
  have hcentop : Subgroup.centralizer ({x} : Set G) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    have hxc : x ∈ Subgroup.center G := by rw [hZtop]; exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hxc g).symm
  have hclass1 : Nat.card (ConjClasses.mk x).carrier = 1 := by
    rw [nat_card_conjClass_carrier_eq_index_centralizer]
    exact (Subgroup.index_eq_one).mpr hcentop
  have h1eq : q ^ d = 1 := by rw [← hclass, hclass1]
  have h2 : 1 < q ^ d := one_lt_pow₀ hq.one_lt (Nat.pos_iff_ne_zero.mp hd)
  omega

/-- **Burnside's `p^a q^b` theorem, core case.**  A finite non-abelian simple group has order divisible by at least three distinct primes; equivalently, no non-abelian simple group has order `p ^ a * q ^ b` for primes `p, q`.

This is the classical character-theoretic theorem (Huppert, *Endliche Gruppen I*, V.7.2 + V.7.3): if `1 ≠ x` has conjugacy class size `q ^ k`, then column orthogonality `∑_{χ ∈ Irr G} χ(1) χ(x) = 0` together with the fact that `χ(x)/χ(1)` is an algebraic integer whenever `q ∤ χ(1)` forces `1/q` to be an algebraic integer.  The algebraic-integrality input is Huppert V.7.1: an average of `d` roots of unity that is integral over `ℤ` is either `0` or has modulus `1`.  The workspace's `Work.CharCore` provides the character theory (`Irr`, `column_orthogonality_not_conj`, `norm_char_le`, `norm_char_eq_iff_isScalar`, `centralChar`, `centralChar_classSum_mul_finrank`, `isIntegral_centralChar_classSum`, `dvd_of_isIntegral_rat`). -/
theorem no_simple_group_of_card_paqb {G : Type*} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnab : ¬ IsMulCommutative G)
    (h : ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ Nat.card G = p ^ a * q ^ b) : False := by
  obtain ⟨p, q, a, b, hp, hq, hcard⟩ := h
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨x, d, hx, hd, hclass⟩ :=
    exists_conjClass_card_prime_pow hsimple hnab hp hq hcard
  obtain ⟨χ, hχ, hne, hqdvd, hval⟩ := exists_irr_not_dvd_deg_char_ne_zero hx hq
  exact false_of_prime_pow_class_chi hsimple hx hq hd hclass hχ hne hqdvd hval

end Work.CharCore
