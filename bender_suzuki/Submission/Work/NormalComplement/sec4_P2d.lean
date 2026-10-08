import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_two
import Submission.Work.NormalComplement.appI_kapp_ncard
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas

The proof of Ch. II §4 Prop. 2 (d) rests on the following ingredients:

* `Kset` is monotone in the subgroup, and an involution `t` normalises `twoPoint H t`
  (`Kset_mono`, `normalizedBy_twoPoint`);
* a proper subgroup of a finite `p`-group is properly contained in its normaliser
  (`lt_inf_normalizer_of_lt`), and the resulting Frattini-type criterion
  (`not_dvd_index_of_relIndex_normalizer`);
* **Appendix II (1)** of Peterfalvi I (p. 203) in the concrete situation of `Ω = G ⧸ H`
  (`exists_sylow_le_twoPoint_of_fixedPts`): a `p`-subgroup of odd prime order `p` whose fixed
  points in `Ω` are exactly the two points `H` and `tH` lies in a `p`-Sylow of `G` contained in
  the two-point stabiliser `D`;
* the auxiliary `normalizer_smul_mem_fixedPts`. -/

/-- `Kset X t = J(X,t)` is monotone in the subgroup `X`. -/
lemma Kset_mono {X Y : Subgroup G} {t : G} (h : X ≤ Y) : Kset X t ⊆ Kset Y t :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-- For an involution `t`, `t` normalises the two-point stabiliser `twoPoint H t = H ⊓ conj t H`. -/
lemma normalizedBy_twoPoint {H : Subgroup G} {t : G} (ht : orderOf t = 2) :
    NormalizedBy t (twoPoint H t) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x hx
  rw [Work.ThreePoints.mem_twoPoint] at hx ⊢
  refine ⟨by simpa [hti] using hx.2, ?_⟩
  have h1 : t⁻¹ * (t * x * t⁻¹) * t = x := by group
  rw [h1]
  exact hx.1

/-- Elements of `N_G(Q)` preserve the set of fixed points of `Q` in `Ω = G ⧸ H`. -/
lemma normalizer_smul_mem_fixedPts {H Q : Subgroup G} {ω : G ⧸ H} (hω : ω ∈ fixedPts H Q)
    {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) : n • ω ∈ fixedPts H Q := by
  rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
  intro y hy
  have hy' : n⁻¹ * y * n ∈ Q := (Subgroup.mem_normalizer_iff''.mp hn y).mp hy
  calc y • (n • ω) = (y * n) • ω := by rw [mul_smul]
    _ = (n * (n⁻¹ * y * n)) • ω := by rw [show y * n = n * (n⁻¹ * y * n) from by group]
    _ = n • ((n⁻¹ * y * n) • ω) := by rw [mul_smul]
    _ = n • ω := by rw [hω _ hy']

/-- **A proper subgroup of a finite `p`-group is properly contained in its normaliser** (the
normalizer condition for `p`-groups): if `Q < S` and `S` is a `p`-group then `Q < S ⊓ N_G(Q)`. -/
lemma lt_inf_normalizer_of_lt {p : ℕ} (hp : p.Prime) {S Q : Subgroup G}
    (hS : IsPGroup p S) (hQS : Q < S) :
    Q < S ⊓ Subgroup.normalizer (Q : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥S := inferInstance
  haveI := hS.isNilpotent
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have htop : (⊤ : Subgroup ↥S).map S.subtype = S := by
    rw [← Subgroup.subgroupOf_self S, Subgroup.subgroupOf_map_subtype, inf_idem]
  have hqmap : (Q.subgroupOf S).map S.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQS.le]
  have hlt : Q.subgroupOf S < (⊤ : Subgroup ↥S) := by
    refine lt_of_le_of_ne le_top ?_
    intro heq
    have hh := congrArg (Subgroup.map S.subtype) heq
    rw [hqmap, htop] at hh
    exact hQS.ne hh
  have hltN := hnc (Q.subgroupOf S) hlt
  have hnot : ¬ (Subgroup.normalizer (Q.subgroupOf S) ≤ Q.subgroupOf S) :=
    fun hsub => hltN.ne (le_antisymm hltN.le hsub)
  obtain ⟨y, hyN, hyQ⟩ := Set.not_subset.mp hnot
  refine lt_of_le_of_ne (fun x hx => ⟨hQS.le hx, Subgroup.le_normalizer hx⟩) ?_
  intro heq
  have hyNorm : (y : G) ∈ Subgroup.normalizer (Q : Set G) := by
    have h1 : y ∈ (Subgroup.normalizer (Q : Set G)).subgroupOf S := by
      rw [Subgroup.subgroupOf_normalizer_eq hQS.le]
      exact hyN
    exact Subgroup.mem_subgroupOf.mp h1
  have hyS : (y : G) ∈ S := y.2
  have hyInQ : (y : G) ∈ Q := by
    rw [heq]
    exact ⟨hyS, hyNorm⟩
  exact hyQ (Subgroup.mem_subgroupOf.mpr hyInQ)

/-- **Frattini-type criterion**: if `Q` is a `p`-subgroup of `G` which is a Sylow `p`-subgroup of
its own normaliser (`p ∤ |N_G(Q) : Q|`), then `Q` is a Sylow `p`-subgroup of `G`
(`p ∤ |G : Q|`). -/
lemma not_dvd_index_of_relIndex_normalizer {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hN : ¬ p ∣ Q.relIndex (Subgroup.normalizer (Q : Set G))) :
    ¬ p ∣ Q.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmax : ∀ T : Subgroup G, Q ≤ T → T ≤ Subgroup.normalizer (Q : Set G) →
      IsPGroup p T → T = Q := by
    intro T hQT hTN hTp
    have hdvd : Q.relIndex T ∣ Q.relIndex (Subgroup.normalizer (Q : Set G)) := by
      have hprod : Q.relIndex T * T.relIndex (Subgroup.normalizer (Q : Set G)) =
          Q.relIndex (Subgroup.normalizer (Q : Set G)) :=
        Subgroup.relIndex_mul_relIndex Q T (Subgroup.normalizer (Q : Set G)) hQT hTN
      rw [← hprod]
      exact dvd_mul_right _ _
    have hnotp : ¬ p ∣ Q.relIndex T := fun h => hN (dvd_trans h hdvd)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
    have hcard : Q.relIndex T ∣ p ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card Q T
    obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hcard
    have hk0 : k = 0 := by
      by_contra hk0
      exact hnotp (hkeq ▸ dvd_pow_self p hk0)
    have h1 : Q.relIndex T = 1 := by rw [hkeq, hk0, pow_zero]
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hQT
  obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow (p := p) hQ
  have hSN : (S : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) = Q :=
    hmax _ (le_inf hQS Subgroup.le_normalizer) inf_le_right (S.isPGroup'.to_le inf_le_left)
  have hSeq : (S : Subgroup G) = Q := by
    by_contra hne
    have hlt : Q < (S : Subgroup G) := lt_of_le_of_ne hQS (Ne.symm hne)
    have hlt' := lt_inf_normalizer_of_lt hp S.isPGroup' hlt
    rw [hSN] at hlt'
    exact absurd hlt' (lt_irrefl Q)
  rw [← hSeq]
  exact Sylow.not_dvd_index S

/-- **Appendix II (1)** of Peterfalvi I (p. 203), in the situation `Ω = G ⧸ H`: if `P` is a
`p`-subgroup of `G` (with `p` an odd prime) whose fixed points in `Ω` are exactly the two points
`H` and `tH`, then there is a `p`-Sylow subgroup `Q` of `G` with `P ≤ Q` and `Q ≤ D`. -/
lemma exists_sylow_le_twoPoint_of_fixedPts {H : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {P : Subgroup G} (hP : IsPGroup r P)
    (hfix : fixedPts H P = {Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)}) :
    ∃ Q : Subgroup G, P ≤ Q ∧ IsPGroup r Q ∧ Q ≤ twoPoint H t ∧ ¬ r ∣ Q.index := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hpt_ne : Work.DoubleTransitivity.pt H ≠ ((t : G) : G ⧸ H) :=
    fun h => htH (Work.DoubleTransitivity.mk_one_eq_iff.mp h.symm)
  -- `P ≤ D`
  have hafix : Work.DoubleTransitivity.pt H ∈ fixedPts H P := by
    rw [hfix]; exact Set.mem_insert _ _
  have hbfix : ((t : G) : G ⧸ H) ∈ fixedPts H P := by
    rw [hfix]; exact Set.mem_insert_of_mem _ rfl
  have hPH : P ≤ H := (Work.DoubleTransitivity.pt_mem_fixedPts_iff P H).mp hafix
  have hPtH : P ≤ Submission.Blueprint.conj t H :=
    (Work.DoubleTransitivity.mk_mem_fixedPts_iff P H t).mp hbfix
  have hPD : P ≤ twoPoint H t := le_inf hPH hPtH
  -- a Sylow `r`-subgroup `T` of `D` containing `P`
  obtain ⟨T, hPT⟩ := IsPGroup.exists_le_sylow (p := r)
    (hP.comap_of_injective (twoPoint H t).subtype Subtype.coe_injective)
  set Qz : Subgroup G := (T : Subgroup ↥(twoPoint H t)).map (twoPoint H t).subtype with hQzdef
  have hQD : Qz ≤ twoPoint H t := Subgroup.map_subtype_le _
  have hPQ : P ≤ Qz := by
    have h1 : (P.subgroupOf (twoPoint H t)).map (twoPoint H t).subtype ≤ Qz :=
      Subgroup.map_mono hPT
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD] at h1
  have hQp : IsPGroup r Qz := T.isPGroup'.map (twoPoint H t).subtype
  have hQrelD : ¬ r ∣ Qz.relIndex (twoPoint H t) := by
    have hsub : Qz.subgroupOf (twoPoint H t) = (T : Subgroup ↥(twoPoint H t)) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t', ht', ht'x⟩
        have h2 : t' = x := Subtype.ext ht'x
        rwa [← h2]
      · intro hx
        exact ⟨x, hx, rfl⟩
    change ¬ r ∣ (Qz.subgroupOf (twoPoint H t)).index
    rw [hsub]
    exact Sylow.not_dvd_index T
  -- the fixed point set of `Q` is still `{H, tH}`
  have hfixQ : fixedPts H Qz = {Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)} := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [← hfix]
      exact Work.ThreePoints.fixedPts_mono hPQ
    · intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact (Work.DoubleTransitivity.pt_mem_fixedPts_iff Qz H).mpr (le_trans hQD inf_le_left)
      · exact (Work.DoubleTransitivity.mk_mem_fixedPts_iff Qz H t).mpr (le_trans hQD inf_le_right)
  set Nz : Subgroup G := Subgroup.normalizer (Qz : Set G) with hNzdef
  -- `N_G(Q) ⊓ H ≤ D`
  have hNHD : Nz ⊓ H ≤ twoPoint H t := by
    intro n hn
    obtain ⟨hnN, hnH⟩ := Subgroup.mem_inf.mp hn
    have hb : ((t : G) : G ⧸ H) ∈ fixedPts H Qz := by
      rw [hfixQ]; exact Set.mem_insert_of_mem _ rfl
    have hnb : n • ((t : G) : G ⧸ H) ∈ fixedPts H Qz :=
      normalizer_smul_mem_fixedPts hb hnN
    rw [hfixQ, Set.mem_insert_iff, Set.mem_singleton_iff] at hnb
    have hnfixa : n • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := by
      refine MulAction.mem_stabilizer_iff.mp ?_
      rw [Work.ThreePoints.stabilizer_mk H 1, Work.DoubleTransitivity.conj_one]
      exact hnH
    have hkey : n • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
      rcases hnb with h | h
      · exfalso
        have h2 : n • ((t : G) : G ⧸ H) = n • Work.DoubleTransitivity.pt H := by rw [h, hnfixa]
        have h3 := congrArg (fun ω : G ⧸ H => n⁻¹ • ω) h2
        have h4 : ((t : G) : G ⧸ H) = Work.DoubleTransitivity.pt H := by
          simpa [smul_smul] using h3
        exact htH (Work.DoubleTransitivity.mk_one_eq_iff.mp h4)
      · exact h
    refine Subgroup.mem_inf.mpr ⟨hnH, ?_⟩
    rw [← Work.ThreePoints.stabilizer_mk H t]
    exact MulAction.mem_stabilizer_iff.mpr hkey
  -- the orbit of `pt H` under `N` is contained in `{H, tH}`
  have horb : MulAction.orbit ↥Nz (Work.DoubleTransitivity.pt H) ⊆
      {Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)} := by
    intro ω hω
    obtain ⟨n, rfl⟩ := hω
    have hb : Work.DoubleTransitivity.pt H ∈ fixedPts H Qz := by
      rw [hfixQ]; exact Set.mem_insert _ _
    have hmem : (n : G) • Work.DoubleTransitivity.pt H ∈ fixedPts H Qz :=
      normalizer_smul_mem_fixedPts hb n.2
    rw [hfixQ] at hmem
    exact hmem
  -- the stabiliser of `pt H` in `N` is `N ⊓ H`
  have hstab : MulAction.stabilizer ↥Nz (Work.DoubleTransitivity.pt H) = (Nz ⊓ H).subgroupOf Nz := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    have hc : n • (Work.DoubleTransitivity.pt H) = (n : G) • (Work.DoubleTransitivity.pt H) := rfl
    rw [hc, ← MulAction.mem_stabilizer_iff, Work.ThreePoints.stabilizer_mk H 1,
      Work.DoubleTransitivity.conj_one]
    exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩
  have hrel : (Nz ⊓ H).relIndex Nz =
      (MulAction.orbit ↥Nz (Work.DoubleTransitivity.pt H)).ncard := by
    change ((Nz ⊓ H).subgroupOf Nz).index =
      (MulAction.orbit ↥Nz (Work.DoubleTransitivity.pt H)).ncard
    rw [← hstab, MulAction.index_stabilizer]
  -- `r ∤ |N : N ⊓ H|`
  have hNH : ¬ r ∣ (Nz ⊓ H).relIndex Nz := by
    have hle2 : (Nz ⊓ H).relIndex Nz ≤ 2 := by
      rw [hrel]
      exact le_trans (Set.ncard_le_ncard horb (Set.toFinite _))
        (le_of_eq (Set.ncard_pair hpt_ne))
    have hpos : 0 < (Nz ⊓ H).relIndex Nz := by
      rw [hrel]
      exact (Set.ncard_pos (s := MulAction.orbit ↥Nz (Work.DoubleTransitivity.pt H))
        (Set.toFinite _)).mpr
        ⟨Work.DoubleTransitivity.pt H, MulAction.mem_orbit_iff.mpr ⟨1, one_smul _ _⟩⟩
    intro hdvd
    exact hr2 (le_antisymm (le_trans (Nat.le_of_dvd hpos hdvd) hle2) hr.two_le)
  -- `r ∤ |N ⊓ H : Q|`
  have hQNH : ¬ r ∣ Qz.relIndex (Nz ⊓ H) := by
    have hle : Qz ≤ Nz ⊓ H := le_inf Subgroup.le_normalizer (le_trans hQD inf_le_left)
    have hprod : Qz.relIndex (Nz ⊓ H) * (Nz ⊓ H).relIndex (twoPoint H t) =
        Qz.relIndex (twoPoint H t) :=
      Subgroup.relIndex_mul_relIndex Qz (Nz ⊓ H) (twoPoint H t) hle hNHD
    intro h
    exact hQrelD (hprod ▸ dvd_trans h (dvd_mul_right _ _))
  have hnrel : ¬ r ∣ Qz.relIndex Nz := by
    have hle : Qz ≤ Nz ⊓ H := le_inf Subgroup.le_normalizer (le_trans hQD inf_le_left)
    have hprod : Qz.relIndex (Nz ⊓ H) * (Nz ⊓ H).relIndex Nz = Qz.relIndex Nz :=
      Subgroup.relIndex_mul_relIndex Qz (Nz ⊓ H) Nz hle inf_le_left
    rw [← hprod]
    exact hr.not_dvd_mul hQNH hNH
  exact ⟨Qz, hPQ, hQp, hQD, not_dvd_index_of_relIndex_normalizer hr hQp hnrel⟩

/-- **Ch. II §4 Prop. 2 (d)** (p.169), which `ChIIFourProp` does not expose: if a prime `r` divides
`|K|` (`K = J(D,t)`, `D = H ⊓ conj t H`) then `D` contains a Sylow `r`-subgroup of `G`.

Route: let `R` be an `r`-Sylow of `D` normalised by `t` (`Work.NormalComplement.appI_two` with
`X = D`, `d = 2`); if `R ≤ V = C_D(t)` then `|D:R| = |D:V|·|V:R|` is divisible by `r`, contradicting
`R` being a Sylow of `D`, while `|D:V| = |K|` (App. I (1)(a) `Work.NormalComplement.appI_one`,
together with the counting `|K| = |Inv H|` from `Work.NormalComplement.bender_prelim` +
`ChIIFourProp` P2(a)); so by App. I (1)(b) applied inside `R` (`t` normalises `R`, `|R|` odd) there
is `1 ≠ x ∈ R ⊓ J(R,t) ⊆ K`; then `x` has exactly two fixed points in `G ⧸ H`
(`ChIIFourProp` P2 (c)), so `R` is an `r`-Sylow of `G` by App. II (1).  (Note `r ≠ 2` is forced by
`r ∣ |K|` and `|D|` odd.) -/
theorem sec4_P2d (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (r : ℕ) (hr : r.Prime)
    (hrK : r ∣ (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t).ncard) :
    ∃ R : Subgroup G, R ≤ Submission.Blueprint.twoPoint H t ∧ IsPGroup r R ∧ ¬ r ∣ R.index := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hD
  -- `D` has odd order, so `r ≠ 2`
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hD]
    exact hH.2.2 t htH
  have hcopD : Nat.Coprime (Nat.card ↥D) 2 := Nat.coprime_two_right.mpr hDodd
  have hnormD : NormalizedBy t D := by
    rw [hD]
    exact normalizedBy_twoPoint ht
  -- App. I (1) applied to `D`: `|K| = |D : V|`
  obtain ⟨hKappIdx, hDcomp⟩ := appI_one (d := 2) Nat.prime_two ht hnormD hcopD
  obtain ⟨hKsetD_eq, -⟩ := hDcomp rfl
  have hrdvdV : r ∣ (Subgroup.centralizer ({t} : Set G) ⊓ D).relIndex D := by
    have h1 : (Kset D t).ncard = (Subgroup.centralizer ({t} : Set G) ⊓ D).relIndex D := by
      rw [← hKsetD_eq, hKappIdx]
      rfl
    rw [← h1, hD]
    exact hrK
  have hrD : r ∣ Nat.card ↥D := by
    have hmul : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ D).subgroupOf D) *
        ((Subgroup.centralizer ({t} : Set G) ⊓ D).subgroupOf D).index = Nat.card ↥D :=
      Subgroup.card_mul_index _
    rw [← hmul]
    exact dvd_mul_of_dvd_right hrdvdV _
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr hrD)
  -- App. I (2): an `r`-Sylow `R` of `D` normalised by `t`
  obtain ⟨⟨R, hRsyl, hRn⟩, -, -⟩ := appI_two (d := 2) Nat.prime_two ht hnormD hcopD (p := r) hr
  have hRD : R ≤ D := hRsyl.2.1
  have hRodd : Odd (Nat.card ↥R) :=
    Work.ThreePoints.Odd.of_dvd (Subgroup.card_dvd_of_le hRD) hDodd
  have hcopR : Nat.Coprime (Nat.card ↥R) 2 := Nat.coprime_two_right.mpr hRodd
  -- `R ⊄ V = C_D(t)`
  have hRnotV : ¬ R ≤ Subgroup.centralizer ({t} : Set G) := by
    intro hRV
    have hRV' : R ≤ Subgroup.centralizer ({t} : Set G) ⊓ D := le_inf hRV hRD
    have hdiv : r ∣ R.relIndex D := by
      have hprod : R.relIndex (Subgroup.centralizer ({t} : Set G) ⊓ D) *
          (Subgroup.centralizer ({t} : Set G) ⊓ D).relIndex D = R.relIndex D :=
        Subgroup.relIndex_mul_relIndex R (Subgroup.centralizer ({t} : Set G) ⊓ D) D hRV' inf_le_right
      rw [← hprod]
      exact dvd_mul_of_dvd_right hrdvdV _
    exact hRsyl.2.2 hdiv
  -- App. I (1)(b) inside `R`: a non-identity element of `R ⊓ J(R,t) ⊆ K`
  obtain ⟨hRKappIdx, hRcomp⟩ := appI_one (d := 2) Nat.prime_two ht hRn hcopR
  obtain ⟨hRKset_eq, hRdecomp⟩ := hRcomp rfl
  obtain ⟨z, hzR, hzC⟩ := Set.not_subset.mp hRnotV
  obtain ⟨⟨c, k⟩, ⟨hcC, hcR, hkKapp, hck⟩, -⟩ := hRdecomp z hzR
  have hkKsetR : k ∈ Kset R t := by rw [← hRKset_eq]; exact hkKapp
  have hkR : k ∈ R := hkKsetR.1
  have hkK : k ∈ invertedBy (Submission.Blueprint.twoPoint H t) t := by
    have h2 : k ∈ Kset D t := Kset_mono hRD hkKsetR
    rwa [hD] at h2
  have hkne : k ≠ 1 := by
    intro hk1
    apply hzC
    have hz : z = c := by rw [← hck, hk1, mul_one]
    rw [hz]
    exact hcC
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := (Work.ThreePoints.mem_invertedBy.mp hkK).1
  have hkH : k ∈ H := (Work.ThreePoints.mem_twoPoint.mp hkD).1
  have hktH : k ∈ Submission.Blueprint.conj t H := by
    rw [Work.ThreePoints.mem_conj_iff]
    exact (Work.ThreePoints.mem_twoPoint.mp hkD).2
  -- P2 (c): `k` fixes exactly two points of `Ω`
  have hkfix2 : (fixedPts H (Subgroup.zpowers k)).ncard = 2 :=
    (hC4 G hS H hH t ht htH).2.2.1 k hkK hkne
  have hpt_ne : Work.DoubleTransitivity.pt H ≠ ((t : G) : G ⧸ H) :=
    fun h => htH (Work.DoubleTransitivity.mk_one_eq_iff.mp h.symm)
  have hfixpair : fixedPts H (Subgroup.zpowers k) =
      {Work.DoubleTransitivity.pt H, ((t : G) : G ⧸ H)} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · exact Set.insert_subset
        ((Work.DoubleTransitivity.pt_mem_fixedPts_iff (Subgroup.zpowers k) H).mpr
          (Subgroup.zpowers_le.mpr hkH))
        (Set.singleton_subset_iff.mpr
          ((Work.DoubleTransitivity.mk_mem_fixedPts_iff (Subgroup.zpowers k) H t).mpr
            (Subgroup.zpowers_le.mpr hktH)))
    · rw [hkfix2, Set.ncard_pair hpt_ne]
  -- App. II (1) with `P = ⟨k⟩`
  have hxP : IsPGroup r (Subgroup.zpowers k) :=
    IsPGroup.to_le hRsyl.1 (Subgroup.zpowers_le.mpr hkR)
  obtain ⟨Q, -, hQp, hQD, hQidx⟩ :=
    exists_sylow_le_twoPoint_of_fixedPts ht htH hr hr2 hxP hfixpair
  exact ⟨Q, hQD, hQp, hQidx⟩

end Work.NormalComplement
