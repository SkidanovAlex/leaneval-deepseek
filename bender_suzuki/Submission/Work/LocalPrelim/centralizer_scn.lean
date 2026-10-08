/-
# `Work.LocalPrelim.centralizer_scn` — FT 3.10 (Thompson)

Feit & Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963), 775–1029,
Chapter I, quoted result **3.10**: if `𝔓` is an `S_p`-subgroup of the group `𝔛` and
`𝔄 ∈ 𝒮𝒞𝒩(𝔓)` (i.e. `𝔄` is a self-centralizing normal abelian subgroup of `𝔓`), then
`C(𝔄) = 𝔄 × 𝔇` with `𝔇` a `p'`-group.

The paper quotes this from Thompson [27] Lemma 5.7, whose proof is character-theoretic.  The
statement is however accessible with purely group-theoretic tools, and this is the route taken here
(suggested in the area's blueprint as "`burnside_npc` in `C(𝔄)`"):

* `C := C_X(A)` centralizes `A`, so `A` is normal (indeed central) in `C`;
* `A = C ∩ P` is exactly the self-centralizing condition `C_X(A) ∩ P ≤ A` of `𝒮𝒞𝒩`, and
  `pSubgroup_le_of_le_centralizer_aux` below shows the stronger statement that *every*
  `p`-subgroup of `C_X(A)` is contained in `A` (so `A` is the Sylow `p`-subgroup of `C_X(A)`):
  a `p`-subgroup of `C_X(A)` lies in a Sylow of `N_X(A)`, and Sylow conjugacy inside `N_X(A)`
  moves it into `P`, where self-centralizingness finishes the job;
* Burnside's normal `p`-complement theorem in the group `C`, applied to the central normal Sylow
  `A` (`Work.LocalPrelim.normal_complement_of_central_sylow`), produces `K ◁ C` complementary
  to `A`; `K` is a `p'`-group because `[C : A] = |K|` is prime to `p`.

Reference: `Submission/Work/ft1963/tex/ch1.md`, quoted result 3.10.
-/
import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.LocalPrelim.normal_complement_of_central_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.LocalPrelim

/-- Every `p`-subgroup of `C_X(A)` is contained in `A`, for `A ∈ 𝒮𝒞𝒩(P)`.  Equivalently, `A` is
the unique Sylow `p`-subgroup of `C_X(A)` (and the `p`-part of `C_X(A)` is `A`).

Proof: let `H = N_X(A)`.  Since `A` is normal in `P`, `P ≤ H`, and since `C_X(A) ≤ H` and
`Q ≤ C_X(A)` also `Q ≤ H`.  A Sylow `R` of `H` contains `Q`; it is conjugate to `P` inside `H`
(Sylow conjugacy in `H`), say `R = P^n` with `n ∈ H`.  Conjugating by `n` moves `Q` into `P`
while `n ∈ N_X(A)` fixes `A`, and `Q` centralizes `A`, so `Q^n ≤ C_X(A) ∩ P = C_P(A) = A`; as `n`
normalizes `A` this gives `Q ≤ A`. -/
private theorem pSubgroup_le_of_le_centralizer_aux {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) {A : Subgroup X} (hA : IsSCN (P : Subgroup X) A)
    {Q : Subgroup X} (hQ : Q ≤ Subgroup.centralizer (A : Set X)) (hQp : IsPGroup p Q) :
    Q ≤ A := by
  classical
  -- the normalizer of `A`, which contains `P` and `C_X(A)`
  set H : Subgroup X := Subgroup.normalizer (A : Set X) with hH
  have hPH : (P : Subgroup X) ≤ H := by
    obtain hnormal := (Subgroup.normal_subgroupOf_iff hA.1).mp hA.2.1
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; exact hnormal a x ha hx
    · intro hax
      have h2 := hnormal (x * a * x⁻¹) x⁻¹ hax (Subgroup.inv_mem _ hx)
      convert h2 using 1
      group
  have hQH : Q ≤ H := hQ.trans (Subgroup.centralizer_le_normalizer (A : Set X))
  have hQHp : IsPGroup p (Q.subgroupOf H) :=
    hQp.comap_of_injective H.subtype Subtype.coe_injective
  obtain ⟨R, hQR⟩ := IsPGroup.exists_le_sylow hQHp
  let PH : Sylow p H := P.subtype hPH
  haveI : Finite (Sylow p ↥H) := Sylow.finite_of_finiteIndex PH
  obtain ⟨n, hn⟩ := (Sylow.isPretransitive_of_finite (p := p) (G := ↥H)).exists_smul_eq R PH
  intro q hq
  have hqH : q ∈ H := hQH hq
  have hqC : q ∈ Subgroup.centralizer (A : Set X) := hQ hq
  have hqR : (⟨q, hqH⟩ : ↥H) ∈ R := hQR (by rw [Subgroup.mem_subgroupOf]; exact hq)
  -- the conjugate of `q` by `n` lies in the Sylow `P` of `H`
  have hmem : (MulAut.conj n) (⟨q, hqH⟩ : ↥H) ∈ (n • R : Sylow p ↥H) := by
    rw [Sylow.smul_def]
    exact Subgroup.mem_map_of_mem _ hqR
  rw [hn] at hmem
  have hPX : (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) ∈ (P : Subgroup X) :=
    Subgroup.mem_subgroupOf.mp
      (show (MulAut.conj n) (⟨q, hqH⟩ : ↥H) ∈ (P : Subgroup X).subgroupOf H from hmem)
  have hw_eq : (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) =
      (n : X) * (q : X) * (n : X)⁻¹ := by
    simp [MulAut.conj_apply]
  -- and it still centralizes `A`, because `n` normalizes `A`
  have hwC : (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) ∈
      Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [hw_eq]
    have hnin : (n : X)⁻¹ ∈ Subgroup.normalizer (A : Set X) := H.inv_mem n.2
    have hã : (n : X)⁻¹ * a * (n : X) ∈ A := by
      have h := ((Subgroup.mem_normalizer_iff.mp hnin) a).mp ha
      simpa using h
    have hqe : (q : X) * ((n : X)⁻¹ * a * (n : X)) =
        ((n : X)⁻¹ * a * (n : X)) * (q : X) :=
      (Subgroup.mem_centralizer_iff.mp hqC ((n : X)⁻¹ * a * (n : X)) hã).symm
    calc a * ((n : X) * (q : X) * (n : X)⁻¹)
        = (n : X) * ((n : X)⁻¹ * a * (n : X)) * (q : X) * (n : X)⁻¹ := by group
      _ = (n : X) * ((q : X) * ((n : X)⁻¹ * a * (n : X))) * (n : X)⁻¹ := by rw [hqe]; group
      _ = ((n : X) * (q : X) * (n : X)⁻¹) * a := by group
  -- self-centralizingness of `A` in `P` now gives `q^n ∈ A`, and `n` normalizes `A`
  have hwA : (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) ∈ A :=
    hA.2.2.2 (Subgroup.mem_inf.mpr ⟨hwC, hPX⟩)
  have hconj : (n : X)⁻¹ * (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) * (n : X) ∈ A := by
    have h := ((Subgroup.mem_normalizer_iff.mp (H.inv_mem n.2)) _).mp hwA
    simpa using h
  have hqX : (q : X) = (n : X)⁻¹ * (((MulAut.conj n) (⟨q, hqH⟩ : ↥H) : ↥H) : X) * (n : X) := by
    rw [hw_eq]; group
  rwa [hqX]

/-- **FT 3.10 (Thompson).**  If `A ∈ 𝒮𝒞𝒩(P)` for a Sylow `p`-subgroup `P` of a finite group `X`,
then `C_X(A) = A × D` with `D` a `p'`-group normal in `C_X(A)` (here `D` is exhibited as a
subgroup of `X`, with `C_X(A) = A ⊔ D`, `A ⊓ D = ⊥` and `D` normal in `C_X(A)`). -/
theorem centralizer_scn {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) {A : Subgroup X} (hA : IsSCN (P : Subgroup X) A) :
    ∃ D : Subgroup X, IsPPrimeGroup p D ∧
      (D.subgroupOf (Subgroup.centralizer (A : Set X))).Normal ∧
      Subgroup.centralizer (A : Set X) = A ⊔ D ∧ A ⊓ D = ⊥ := by
  classical
  -- notation: `C` is the centralizer of `A` in `X`
  set C : Subgroup X := Subgroup.centralizer (A : Set X) with hC
  -- `A` is abelian, hence `A ≤ C_X(A)`
  have hAC : A ≤ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    simpa using hA.2.2.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩
  -- the self-centralizing condition: `C_X(A) ∩ P = A`
  have hA_eq : A = C ⊓ P := le_antisymm (le_inf hAC hA.1) hA.2.2.2
  -- `A` is a `p`-group, and so is `A` viewed inside `C`
  have hAp : IsPGroup p A := P.isPGroup'.to_le hA.1
  have hApC : IsPGroup p (A.subgroupOf C) := hAp.comap_of_injective C.subtype Subtype.coe_injective
  -- `A` is normal in `C` (indeed central there)
  have hAnC : (A.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAC]
    intro h k hh hk
    have hcomm : h * k = k * h := (Subgroup.mem_centralizer_iff.mp hk) h hh
    rw [show k * h * k⁻¹ = h from by rw [hcomm.symm]; group]
    exact hh
  -- `A` is a Sylow `p`-subgroup of `C`: every `p`-subgroup of `C` lies in `A`, so a Sylow of `C`
  -- must equal `A` (viewed as a subgroup of `C`), and its index is prime to `p`.
  have hnotdvd : ¬ p ∣ (A.subgroupOf C).index := by
    obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥C)
    have hSle : A.subgroupOf C ≤ (S : Subgroup C) := IsPGroup.le_sylow_of_normal hApC S
    have hQp : IsPGroup p ((S : Subgroup C).map C.subtype) := S.isPGroup'.map C.subtype
    have hQC : ((S : Subgroup C).map C.subtype) ≤ C := Subgroup.map_subtype_le (S : Subgroup C)
    have hQA : ((S : Subgroup C).map C.subtype) ≤ A :=
      pSubgroup_le_of_le_centralizer_aux P hA hQC hQp
    have hSleA : (S : Subgroup C) ≤ A.subgroupOf C := by
      change (S : Subgroup C) ≤ Subgroup.comap C.subtype A
      exact (Subgroup.map_le_iff_le_comap).mp hQA
    have hSeq : (S : Subgroup C) = A.subgroupOf C := le_antisymm hSleA hSle
    have hnd : ¬ p ∣ (S : Subgroup C).index := Sylow.not_dvd_index S
    rwa [hSeq] at hnd
  -- `A` is central in `C` (that is what `C = C_X(A)` means)
  have hcen : (A.subgroupOf C) ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subtype.ext ?_
    have hxA : ((x : C) : X) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have hcomm := (Subgroup.mem_centralizer_iff.mp y.2) ((x : C) : X) hxA
    simpa using hcomm.symm
  -- Burnside's normal `p`-complement theorem in the group `C`
  obtain ⟨K, hKn, hKc⟩ :=
    normal_complement_of_central_sylow (A.subgroupOf C) hApC hnotdvd hcen
  refine ⟨K.map C.subtype, ?_, ?_, ?_, ?_⟩
  · -- `D = K` (as a subgroup of `X`) is a `p'`-group
    show Work.Hall.IsPiNat (fun q => q ≠ p) (Nat.card ↥(K.map C.subtype))
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    have hnotpK : ¬ p ∣ Nat.card ↥K := by
      rw [← hKc.symm.index_eq_card]
      exact hnotdvd
    intro q _ hdvd hqp
    exact hnotpK (hqp ▸ hdvd)
  · -- `K ◁ C` translates into `(K.map C.subtype).subgroupOf C = K ◁ C`
    rw [show (K.map C.subtype).subgroupOf C = K from
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K]
    exact hKn
  · -- `C = A ⊔ K` from the complement condition inside `C`
    have htop : (A.subgroupOf C) ⊔ K = ⊤ := hKc.sup_eq_top
    have hmap := congrArg (Subgroup.map C.subtype) htop
    simp only [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at hmap
    rw [Subgroup.subgroupOf_map_subtype A C, inf_eq_left.mpr hAC] at hmap
    exact hmap.symm
  · -- `A ⊓ K = ⊥`
    have hbot : (A.subgroupOf C) ⊓ K = ⊥ := disjoint_iff.mp hKc.disjoint
    have hmap := congrArg (Subgroup.map C.subtype) hbot
    rw [Subgroup.map_inf (A.subgroupOf C) K C.subtype C.subtype_injective, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype A C, inf_eq_left.mpr hAC] at hmap
    exact hmap

end Work.LocalPrelim
