import Mathlib
import Submission.Work.DSTR.Defs

/-!
# DSTR leaf L19 (Bender 1981, 1.9)

A perfect finite group `E` with `E / Z(E) ≃ L₂(q)` (`q = pᵏ` odd, `≥ 5`), `Z(E)` odd and of order
prime to `p`, has `Z(E) = 1`.

The proof is the classical transfer argument.

* If `Z(E) ≠ 1`, then (as `Z(E)` is a finite abelian group of odd order) some odd prime `r` divides
  `|Z(E)|`, and by Cauchy's theorem `Z(E)` has an element `w` of order `r`; note `r ≠ p` because
  `|Z(E)|` is prime to `p`, and `r ≠ 2` because `|Z(E)|` is odd.
* A Sylow `r`-subgroup `R` of `E` is abelian: `R ∩ Z(E) ≤ Z(R)` and `R / (R ∩ Z(E))` embeds in
  `E/Z(E) ≃ L₂(q)`; being an `r`-subgroup (`r ≠ 2`, `r ≠ p`) it is contained in a Sylow
  `r`-subgroup of `L₂(q)`, which is cyclic by `hL2`, hence `R/(R∩Z(E))` is cyclic, and a group
  whose quotient by a central subgroup is cyclic is abelian.
* The transfer `V : E →* R` (defined since `R` is abelian) lands in an abelian group and `E` is
  perfect, so `V` is trivial; but on the central element `w` we have `V w = w ^ [E : R]`. Hence
  `w ^ [E : R] = 1`, i.e. `r = orderOf w ∣ [E : R]`, contradicting `r ∤ [E : R]` for a Sylow
  `r`-subgroup.
-/

open scoped MatrixGroups
open scoped IsMulCommutative

set_option linter.style.haveILetI false

namespace Work.DSTR

/-- A homomorphism whose kernel lies in the centre and whose *range* is cyclic has abelian domain.
(A variation of `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` that only needs the
range, not the whole codomain, to be cyclic.) -/
private lemma isMulCommutative_of_isCyclic_range {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hcyc : IsCyclic f.range) (hf : f.ker ≤ Subgroup.center G) : IsMulCommutative G := by
  haveI : IsCyclic f.range := hcyc
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (f.codRestrict f.range (fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩)) ?_
  rw [MonoidHom.ker_codRestrict f f.range _]
  exact hf

/-- If a Sylow `r`-subgroup `R` of `E` has cyclic image in `E / Z(E)`, then `R` is abelian:
the kernel of `R → E / Z(E)` is `R ∩ Z(E) ≤ Z(R)`, and `R / (R ∩ Z(E))` is cyclic. -/
private lemma sylow_isMulCommutative_of_cyclic_image {E : Type*} [Group E] [Finite E]
    (r : ℕ) (R : Sylow r E)
    (hcyc : IsCyclic (Subgroup.map (QuotientGroup.mk' (Subgroup.center E)) (R : Subgroup E))) :
    IsMulCommutative (R : Subgroup E) := by
  let Z := Subgroup.center E
  let f : (R : Subgroup E) →* E ⧸ Z := (QuotientGroup.mk' Z).comp (R : Subgroup E).subtype
  have hrange : f.range = Subgroup.map (QuotientGroup.mk' Z) (R : Subgroup E) := by
    simp only [f, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcyc' : IsCyclic f.range := by rw [hrange]; exact hcyc
  have hker : f.ker ≤ Subgroup.center (R : Subgroup E) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : f x = 1 := MonoidHom.mem_ker.mp hx
    have hx2 : (QuotientGroup.mk' Z) (x : E) = 1 := hx1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
    simpa using Subgroup.mem_center_iff.mp hx2 (y : E)
  exact isMulCommutative_of_isCyclic_range f hcyc' hker

/-- The transfer argument in isolation: in a finite perfect group `E`, a central element `z` and an
abelian subgroup `H` of finite index satisfy `z ^ [E : H] = 1` (because the transfer `E →* H`
vanishes on `E = E'` and equals the `[E : H]`-th power map on central elements). -/
private lemma pow_index_eq_one_of_mem_center {E : Type*} [Group E] [Finite E] (H : Subgroup E)
    [H.FiniteIndex] [IsMulCommutative H] (hE : Group.IsPerfect E) {z : E}
    (hz : z ∈ Subgroup.center E) : z ^ H.index = 1 := by
  have htriv : MonoidHom.transfer (MonoidHom.id H) z = 1 := by
    have h : commutator E ≤ (MonoidHom.transfer (MonoidHom.id H)).ker :=
      Abelianization.commutator_subset_ker _
    rw [Group.IsPerfect.commutator_eq_top] at h
    exact MonoidHom.mem_ker.mp (h trivial)
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hzk
    rw [hzk g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hp := MonoidHom.transfer_eq_pow (MonoidHom.id H) z key
  rw [htriv] at hp
  exact Subtype.ext_iff.mp hp.symm

/-- The `L₂(q)` input: for an odd prime `r ≠ p`, the image of a Sylow `r`-subgroup of `E` in
`E / Z(E) ≃ L₂(q)` is cyclic (`hL2` says the Sylow `r`-subgroups of `L₂(q)` are cyclic). -/
private lemma image_sylow_isCyclic {E : Type*} [Group E] [Finite E] (p k : ℕ) [Fact p.Prime]
    (hp : Odd p) (h5 : 5 ≤ p ^ k) (hL2 : Work.GW2.L2OddSylowCyclicProp)
    (φ : E ⧸ Subgroup.center E ≃* PSL(2, GaloisField p k))
    (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) (hrp : r ≠ p) (R : Sylow r E) :
    IsCyclic (Subgroup.map (QuotientGroup.mk' (Subgroup.center E)) (R : Subgroup E)) := by
  let Z := Subgroup.center E
  let A : Subgroup (E ⧸ Z) := Subgroup.map (QuotientGroup.mk' Z) (R : Subgroup E)
  have hA : IsPGroup r A := IsPGroup.map R.isPGroup' (QuotientGroup.mk' Z)
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  have hT : IsPGroup r (Subgroup.map φ.toMonoidHom (S : Subgroup (E ⧸ Z))) :=
    IsPGroup.map S.isPGroup' φ.toMonoidHom
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup (PSL(2, GaloisField p k))) :=
    hL2 p k hp h5 r hr2 hrp Q
  have hTc : IsCyclic (Subgroup.map φ.toMonoidHom (S : Subgroup (E ⧸ Z))) :=
    Subgroup.isCyclic_of_le hTQ
  have hSc : IsCyclic (S : Subgroup (E ⧸ Z)) :=
    (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (S : Subgroup (E ⧸ Z)) φ.toMonoidHom φ.injective)).mpr hTc
  exact Subgroup.isCyclic_of_le hAS

/-- **L19** (`Work.GW2.L19Prop`, Bender 1981 1.9): a perfect group `E` with `E/Z(E) = L_2(q)` (`q = p^k` odd, `>= 5`), `Z(E)` odd and prime to `p`, has `Z(E) = 1`.  The transfer argument: for an odd prime `r | |Z(E)|`, a Sylow `r`-subgroup `R` of `E` is abelian because `R/(R cap Z(E))` is a cyclic Sylow of `L_2(q)` (`hL2`); the transfer `E -> R` is trivial on `E = E'`, so `z ^ |E : R| = 1` for `z` central of order `r`, and `|E : R|` is prime to `r`. -/
theorem l19 (hL2 : Work.GW2.L2OddSylowCyclicProp) : Work.GW2.L19Prop := by
  intro E instG instF p k instPrime hpOdd h5 hperf hiso hZodd hZcop
  classical
  by_contra hZne
  -- `Z(E)` is a nontrivial finite group; pick a prime `r` dividing its order.
  have hcard : Nat.card (Subgroup.center E) ≠ 1 := fun h =>
    hZne (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact r.Prime := ⟨hrp⟩
  -- `r` is odd and `r ≠ p`.
  have hr2 : r ≠ 2 := by
    intro h
    have hev : Even (Nat.card (Subgroup.center E)) := by
      rw [even_iff_two_dvd, ← h]; exact hrdvd
    exact (Nat.not_even_iff_odd.mpr hZodd) hev
  have hrp' : r ≠ p := by
    intro h
    have h1 : r ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hZcop]
      exact Nat.dvd_gcd hrdvd (h ▸ dvd_refl r)
    have hle := Nat.le_of_dvd (by norm_num) h1
    have := hrp.two_le
    omega
  -- Cauchy: an element of order `r`, central.
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hwE : (w : E) ∈ Subgroup.center E := w.2
  have hword : orderOf (w : E) = r := by rw [Subgroup.orderOf_coe, hw]
  obtain ⟨φ⟩ := hiso
  let R : Sylow r E := default
  haveI : (R : Subgroup E).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- `R` is abelian, since its image in `E/Z(E) ≃ L₂(q)` is cyclic.
  have hcyc : IsCyclic (Subgroup.map (QuotientGroup.mk' (Subgroup.center E)) (R : Subgroup E)) :=
    image_sylow_isCyclic p k hpOdd h5 hL2 φ r hr2 hrp' R
  have habel : IsMulCommutative (R : Subgroup E) := sylow_isMulCommutative_of_cyclic_image r R hcyc
  haveI : IsMulCommutative (R : Subgroup E) := habel
  -- The transfer `E →* R` is trivial on the perfect group `E`, so `w ^ [E : R] = 1`.
  have hperf' : Group.IsPerfect E := ⟨by rw [commutator_def]; exact hperf⟩
  have hpR : (w : E) ^ (R : Subgroup E).index = 1 :=
    pow_index_eq_one_of_mem_center (R : Subgroup E) hperf' hwE
  have hdvd' : orderOf (w : E) ∣ (R : Subgroup E).index := orderOf_dvd_iff_pow_eq_one.mpr hpR
  rw [hword] at hdvd'
  exact (Sylow.not_dvd_index R) hdvd'

end Work.DSTR
