import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.BRel_witness_facts
import Submission.Work.BMAX.commutator_pCoreIn_inf_pResidualIn_fstarIn
import Submission.Work.BMAX.commutator_pCoreIn_inf_fittingIn_eq_bot
import Submission.Work.BMAX.fstarIn_le_pResidualIn_of_notMem_primesOf
import Submission.Work.BMAX.eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot
import Submission.Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup

set_option linter.style.haveILetI false

/-!
# BMAX — `π(F(A)) = π(F(B))` for maximal `D`-groups with `A ⇝ B` and `B ⇝ A`

Target (verbatim, as requested by the prover of `BMAX/Bender17iiiCond`):

`theorem Work.BMAX.GWPiEq (T : LocalToolkit) (G) [Group G] [Finite G] (hG : IsSimpleGroup G)
(A B : Subgroup G) ... (hcA : IsCoatom A) (hBne : B ≠ ⊤) (hrelAB : BRel A B)
(hcB : IsCoatom B) (hrelBA : BRel B A) :
  primesOf (fittingIn A) = primesOf (fittingIn B)`

## Mathematics

This is the `π`-equality step of Bender 1970, 1.6, in the `⇝`-setting of Bender 1981,
Lemma 2.3.  Write `π = π(F(A)) = primesOf (fittingIn A)` and `σ = π(F(B))`.

* For `p ∈ π` the `p`-core `O_p(A)` is non-trivial (`pCoreIn_eq_bot_iff_not_mem_primesOf`).
* Since `A` is a `D`-group and `B` a coatomic subgroup with `B ⇝ A`, Bender's 1.7(ii)
  in the prime-by-prime form `pCoreIn_inf_coatom_eq_bot'` gives `O_p(A) ∩ B = ⊥` for every
  prime `p ∉ σ`.
* Since `A ⇝ B` is witnessed by some `X ≤ F(A)`, we get `Z(F(A)) ≤ B`
  (`BRel_witness_facts`: `Z(F(A))` centralizes `F(A) ⊇ X`, hence normalizes `X`, hence lies
  in `N_G(X) ∩ F*(A) ≤ B`).
* `F(A)` is nilpotent, so `Z(F(A)) ∩ O_p(A) ≠ 1` for every prime `p ∈ π`
  (`zcenterIn_inf_pCoreIn_ne_bot`: a nilpotent group of order divisible by `p` has a
  non-trivial centre, which meets `O_p(A)` — equivalently `O_p(A)` is the Sylow `p`-subgroup
  of `F(A)` and the Sylow `p`-subgroup of a nilpotent group has non-trivial centre).

Now if `p ∈ π \ σ`, then `Z(F(A)) ∩ O_p(A) ⊆ O_p(A) ∩ B = ⊥` is trivial, a contradiction.
Hence `π ⊆ σ`, and by symmetry `σ ⊆ π`.

Note that no hypothesis `A ≠ B` is needed: the two inclusions are established by
contradiction on the existence of `p` in one set and not the other, which is impossible
when `A = B`.
-/

namespace Work.BMAX

open Subgroup

/-! ## 1. Tools copied out of `Bender17DGroupMain` (whose module currently does not build)

The two lemmas `centralizer_fstarIn_inf_le'` and `pCoreIn_inf_coatom_eq_bot'` are the
statements of `Work.BMAX.centralizer_fstarIn_inf_le` and
`Work.BMAX.pCoreIn_inf_coatom_eq_bot` of `Submission/Work/BMAX/Bender17DGroupMain.lean`,
reproved here under primed names so that the present module does not have to import the
(under construction) module `commutator_pCoreIn_pResidualIn_witness` on which that file
depends.  Their proofs are copied verbatim. -/

variable {G : Type} [Group G] [Finite G]

/-- `FStarProp` of the toolkit, transported to the ambient group: the centralizer in `A` of
`F*(A)` lies in `F*(A)`. -/
theorem centralizer_fstarIn_inf_le' (T : Work.GW2.LocalToolkit) (A : Subgroup G)
    (hdih : Work.GW2.DihOrCycSylow ↥A) (hD : Work.GW2.IsDGroup ↥A) :
    Subgroup.centralizer (Work.GW2.fstarIn A : Set G) ⊓ A ≤ Work.GW2.fstarIn A := by
  classical
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have h := T.fstar ↥A T.ft hdih hD
  refine Subgroup.mem_map.mpr ⟨⟨x, hx2⟩, h ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp hx1) (y : G) ⟨y, hy, rfl⟩

/-- Bender 1981, Lemma 2.3(ii), prime by prime: for `q ∉ π(F(A))` the `q`-core of `B` meets
`A` trivially. -/
theorem pCoreIn_inf_coatom_eq_bot' (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G)
    (A B X : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_dih : Work.GW2.DihOrCycSylow ↥A) (hA_D : Work.GW2.IsDGroup ↥A)
    (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    (q : ℕ) (hq : q.Prime) (hqpi : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Work.GW2.pCoreIn q B ⊓ A = ⊥ := by
  classical
  have hmain := commutator_pCoreIn_inf_pResidualIn_fstarIn hG A B X hA hB hA_D hX hSB hSl
    q hq hqpi
  have hfstar_le := fstarIn_le_pResidualIn_of_notMem_primesOf A q hq hqpi
  have hQc : Work.GW2.pCoreIn q B ⊓ A ≤
      Subgroup.centralizer (Work.GW2.fstarIn A : Set G) :=
    le_trans ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hmain)
      (Subgroup.centralizer_le hfstar_le)
  have hQf : Work.GW2.pCoreIn q B ⊓ A ≤ Work.GW2.fstarIn A :=
    le_trans (le_inf hQc inf_le_right)
      (centralizer_fstarIn_inf_le' T A hA_dih hA_D)
  have hQF : (Work.GW2.pCoreIn q B ⊓ A) ⊓ Work.GW2.fittingIn A = ⊥ := by
    have h1 : (Work.GW2.pCoreIn q B ⊓ A) ⊓ Work.GW2.fittingIn A ≤
        Work.GW2.pCoreIn q A :=
      inf_fittingIn_le_pCoreIn_of_le_pCoreIn A B (Work.GW2.pCoreIn q B ⊓ A) q hq
        inf_le_left inf_le_right
    have h2 : Work.GW2.pCoreIn q A = ⊥ :=
      (pCoreIn_eq_bot_iff_not_mem_primesOf A q hq).mpr hqpi
    exact le_bot_iff.mp (h2 ▸ h1)
  exact eq_bot_of_le_fstarIn_of_inf_fittingIn_eq_bot A (Work.GW2.pCoreIn q B ⊓ A) hQf hQF hQc

/-! ## 2. `Z(F(A)) ∩ O_p(A) ≠ 1` when `p ∈ π(F(A))`

`F(A)` is nilpotent; `O_p(A)` is its (unique) Sylow `p`-subgroup, and the Sylow
`p`-subgroup of a finite nilpotent group has a non-trivial centre.  Any such central element
`z ≠ 1` has order `p`, and since it lies in the normal nilpotent subgroup `F(A) ⊴ ↥A` it
lies in `O_p(A)` by `mem_pCore_of_mem_normal_isNilpotent_of_isPGroup`. -/

theorem zcenterIn_inf_pCoreIn_ne_bot (A : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Work.GW2.zcenterIn (Work.GW2.fittingIn A) ⊓ Work.GW2.pCoreIn p A ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- the Fitting subgroup of `↥A`, its nilpotence and normality
  have hFnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥A) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥A)]
    infer_instance
  have hFnorm : (Work.GW2.fitting ↥A).Normal := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥A)]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥A
  -- `p ∣ |F(A)|`
  have hcard : Nat.card ↥(Work.GW2.fittingIn A) = Nat.card ↥(Work.GW2.fitting ↥A) :=
    Subgroup.card_map_of_injective A.subtype_injective (K := Work.GW2.fitting ↥A)
  have hpdvd : p ∣ Nat.card ↥(Work.GW2.fitting ↥A) := by
    rw [← hcard]
    exact (Nat.mem_primeFactors.mp hpi).2.1
  -- the centre of `F(A)` has order divisible by `p`
  have hzdvd : p ∣ Nat.card ↥(Subgroup.center ↥(Work.GW2.fitting ↥A)) :=
    Group.IsNilpotent.prime_dvd_card_center hpdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hzdvd
  -- an element `xF` of `F(A)` of order `p`, central in `F(A)`
  set xF : ↥(Work.GW2.fitting ↥A) := (c : ↥(Work.GW2.fitting ↥A)) with hxFdef
  have hxcF : xF ∈ Subgroup.center ↥(Work.GW2.fitting ↥A) := by
    rw [hxFdef]; exact c.2
  have hxordF : orderOf xF = p := by
    rw [hxFdef]
    exact (orderOf_injective (Subgroup.subtype (Subgroup.center ↥(Work.GW2.fitting ↥A)))
      (Subgroup.subtype_injective _) c).trans hc
  -- the same element inside `↥A`
  have hxord : orderOf (xF : ↥A) = p :=
    (orderOf_injective (Subgroup.subtype (Work.GW2.fitting ↥A))
      (Subgroup.subtype_injective _) xF).trans hxordF
  -- hence it generates a `p`-subgroup and so lies in `O_p(A)`
  have hxpg : IsPGroup p ↥(Subgroup.zpowers (xF : ↥A)) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hxord, pow_one]⟩
  have hxcore : (xF : ↥A) ∈ Work.GW2.pCore p ↥A :=
    mem_pCore_of_mem_normal_isNilpotent_of_isPGroup hFnorm hFnil xF.2 hxpg
  -- the ambient element `z = A.subtype xF`
  set z : G := A.subtype (xF : ↥A) with hzdef
  have hzfit : z ∈ Work.GW2.fittingIn A :=
    Subgroup.mem_map.mpr ⟨(xF : ↥A), xF.2, rfl⟩
  have hzcore : z ∈ Work.GW2.pCoreIn p A :=
    Subgroup.mem_map.mpr ⟨(xF : ↥A), hxcore, rfl⟩
  have hzcen : z ∈ Work.GW2.zcenterIn (Work.GW2.fittingIn A) := by
    refine ⟨hzfit, fun w hw => ?_⟩
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    show z * A.subtype w' = A.subtype w' * z
    rw [hzdef]
    have hcomm : (xF : ↥A) * w' = w' * (xF : ↥A) := by
      have h := (Subgroup.mem_center_iff.mp hxcF (⟨w', hw'⟩ : ↥(Work.GW2.fitting ↥A))).symm
      simpa using congrArg (Subtype.val) h
    rw [← map_mul, ← map_mul, hcomm]
  have hzmem : z ∈ Work.GW2.zcenterIn (Work.GW2.fittingIn A) ⊓ Work.GW2.pCoreIn p A :=
    ⟨hzcen, hzcore⟩
  -- `z ≠ 1` because it has order `p`
  have hzne : z ≠ 1 := by
    intro h1
    have h2 : A.subtype (xF : ↥A) = 1 := hzdef ▸ h1
    have hx1 : (xF : ↥A) = 1 := A.subtype_injective (by rw [h2, map_one])
    have hord1 : orderOf (xF : ↥A) = 1 := by rw [hx1, orderOf_one]
    rw [hxord] at hord1
    exact hp.ne_one hord1
  intro hbot
  exact hzne (Subgroup.mem_bot.mp (hbot ▸ hzmem))

/-! ## 3. The main theorem -/

theorem GWPiEq (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G]
    (hG : IsSimpleGroup G) (A B : Subgroup G)
    (hAsyl : Work.GW2.DihOrCycSylow A) (hDA : Work.GW2.IsDGroup A)
    (hBsyl : Work.GW2.DihOrCycSylow B) (hDB : Work.GW2.IsDGroup B)
    (hcA : IsCoatom A) (hBne : B ≠ ⊤) (hrelAB : Work.GW2.BRel A B)
    (hcB : IsCoatom B) (hrelBA : Work.GW2.BRel B A) :
    Work.GW2.primesOf (Work.GW2.fittingIn A) = Work.GW2.primesOf (Work.GW2.fittingIn B) := by
  classical
  -- witnesses of the two relations, for the prime-by-prime clause of Bender 1.7(ii)
  obtain ⟨XA, hXAF, hSBA, hSlA, hZA, -⟩ := BRel_witness_facts A B hrelAB
  obtain ⟨XB, hXBF, hSBB, hSlB, hZB, -⟩ := BRel_witness_facts B A hrelBA
  -- `Z(F(A)) ≤ B` and `Z(F(B)) ≤ A`
  have hZA_le : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ B :=
    le_trans (le_inf hZA (Work.GW2.zcenterIn_le (Work.GW2.fittingIn A) |>.trans
      (Work.GW2.fittingIn_le_fstarIn A))) hSBA
  have hZB_le : Work.GW2.zcenterIn (Work.GW2.fittingIn B) ≤ A :=
    le_trans (le_inf hZB (Work.GW2.zcenterIn_le (Work.GW2.fittingIn B) |>.trans
      (Work.GW2.fittingIn_le_fstarIn B))) hSBB
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · -- `p ∈ π(F(A)) ⟹ p ∈ π(F(B))`
    by_contra hpn
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    -- Bender 1.7(ii) applied to the pair `(B, A)`: `O_p(A) ∩ B = ⊥`
    have hinf : Work.GW2.pCoreIn p A ⊓ B = ⊥ :=
      pCoreIn_inf_coatom_eq_bot' T hG B A XB hcB hcA.ne_top hBsyl hDB hXBF hSBB hSlB
        p hpprime hpn
    -- but `Z(F(A)) ∩ O_p(A) ≠ 1` lies in `B ∩ O_p(A)`
    have hZ := zcenterIn_inf_pCoreIn_ne_bot A p hpprime hp
    have hle : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ⊓ Work.GW2.pCoreIn p A ≤
        Work.GW2.pCoreIn p A ⊓ B :=
      le_inf inf_le_right (le_trans inf_le_left hZA_le)
    rw [hinf] at hle
    exact hZ (le_bot_iff.mp hle)
  · -- `p ∈ π(F(B)) ⟹ p ∈ π(F(A))`
    by_contra hpn
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hinf : Work.GW2.pCoreIn p B ⊓ A = ⊥ :=
      pCoreIn_inf_coatom_eq_bot' T hG A B XA hcA hBne hAsyl hDA hXAF hSBA hSlA
        p hpprime hpn
    have hZ := zcenterIn_inf_pCoreIn_ne_bot B p hpprime hp
    have hle : Work.GW2.zcenterIn (Work.GW2.fittingIn B) ⊓ Work.GW2.pCoreIn p B ≤
        Work.GW2.pCoreIn p B ⊓ A :=
      le_inf inf_le_right (le_trans inf_le_left hZB_le)
    rw [hinf] at hle
    exact hZ (le_bot_iff.mp hle)

end Work.BMAX
