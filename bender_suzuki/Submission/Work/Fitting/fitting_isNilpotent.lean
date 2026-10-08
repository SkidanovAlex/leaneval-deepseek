import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fitting subgroup of a finite group is nilpotent

`F(G)` is defined in `Submission.Work.Fitting.Defs` as the supremum of the normal
nilpotent subgroups of `G`.  We show that `F(G)` is nilpotent.

The mathematical content is **Fitting's theorem**: the join of two normal nilpotent
subgroups is nilpotent.  We prove the finite case (`nilpotent_sup_of_normal_finite`)
by induction on the cardinality of the ambient group `X`: for normal nilpotent
`H K ≤ X` we quotient `X` by the centre `Z(H)` of `H` (a non-trivial normal
subgroup of `X`, whence the quotient is strictly smaller) and apply the induction
hypothesis to the images of `H` and `K`.  This shows that some term of the lower
central series of `H ⊔ K` lies in `Z(H)`; doing the same with `Z(K)` shows that
some term lies in `Z(H) ⊓ Z(K)`, which is central in `H ⊔ K`, so the next term
vanishes.

Since the subgroups of a finite group form a finite set, and `fittingSet G` is
closed under binary joins and contains `⊥`, its supremum is again one of its
members, hence nilpotent.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.Fitting

variable {X : Type*} [Group X]

/-- The centre of a subgroup `H`, viewed as a subgroup of the ambient group. -/
def subCenter (H : Subgroup X) : Subgroup X := (Subgroup.center ↥H).map H.subtype

theorem subCenter_normal {H : Subgroup X} (hH : H.Normal) : (subCenter H).Normal where
  conj_mem := by
    intro a ha b
    rw [subCenter] at ha ⊢
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨b * (h : X) * b⁻¹, hH.conj_mem h h.2 b⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff] at hh ⊢
    intro y
    apply Subtype.ext
    have hcomm := congrArg Subtype.val
      (hh ⟨b⁻¹ * (y : X) * b, by simpa using hH.conj_mem (y : X) y.2 b⁻¹⟩)
    simp only [Subgroup.coe_mul] at hcomm
    calc (y : X) * (b * (h : X) * b⁻¹)
        = b * ((b⁻¹ * (y : X) * b) * (h : X)) * b⁻¹ := by group
      _ = b * ((h : X) * (b⁻¹ * (y : X) * b)) * b⁻¹ := by rw [hcomm]
      _ = (b * (h : X) * b⁻¹) * (y : X) := by group

theorem subCenter_ne_bot {H : Subgroup X} [Nontrivial ↥H] [Group.IsNilpotent ↥H] :
    subCenter H ≠ ⊥ := by
  intro hbot
  rw [subCenter] at hbot
  have hle : Subgroup.center ↥H ≤ (H.subtype : ↥H →* X).ker :=
    (Subgroup.map_eq_bot_iff (f := H.subtype) (Subgroup.center ↥H)).mp hbot
  rw [Subgroup.ker_subtype] at hle
  exact Group.IsNilpotent.center_ne_bot ↥H (le_bot_iff.mp hle)

theorem subCenter_le_centralizer (H : Subgroup X) :
    subCenter H ≤ Subgroup.centralizer (H : Set X) := by
  intro z hz
  rw [subCenter] at hz
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hh ⟨y, hy⟩)

/-- A homomorphic image of a nilpotent group is nilpotent. -/
theorem isNilpotent_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (h : Group.IsNilpotent ↥H) : Group.IsNilpotent ↥(H.map f) := by
  haveI := h
  let g : ↥H →* ↥(H.map f) :=
    { toFun := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Group.nilpotent_of_surjective g hg

/-- If the images of `H` and `K` in the quotient by a normal subgroup `N` generate a
nilpotent subgroup, then some term of the lower central series of `H ⊔ K` is contained
in `N`. -/
theorem exists_lcs_le_of_quotient_nilpotent (H K N : Subgroup X) [N.Normal]
    (hQ : Group.IsNilpotent ↥((H.map (QuotientGroup.mk' N)) ⊔ (K.map (QuotientGroup.mk' N)))) :
    ∃ m, (H ⊔ K).lowerCentralSeries m ≤ N := by
  obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries _).mp hQ
  refine ⟨m, ?_⟩
  have hm' : ((H ⊔ K).lowerCentralSeries m).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_lowerCentralSeries, Subgroup.map_sup]
    exact hm
  have h2 := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' N) _).mp hm'
  rwa [QuotientGroup.ker_mk'] at h2

/-- **Fitting's theorem** (finite case): the join of two normal nilpotent subgroups of a
finite group is nilpotent.  Proved by induction on the cardinality of the ambient group. -/
theorem pair_aux (n : ℕ) :
    ∀ (X : Type*) [Group X] [Finite X], Nat.card X ≤ n →
      ∀ (H K : Subgroup X), H.Normal → K.Normal → Group.IsNilpotent ↥H → Group.IsNilpotent ↥K →
        Group.IsNilpotent ↥(H ⊔ K) := by
  induction n with
  | zero =>
    intro X _ _ hcard H K hH hK iH iK
    exact absurd hcard
      (not_le.mpr (Nat.pos_of_ne_zero (by rw [Nat.card_ne_zero]; exact ⟨⟨1⟩, inferInstance⟩)))
  | succ n ih =>
    intro X _ fX hcard H K hH hK iH iK
    by_cases hle : Nat.card X ≤ n
    · exact ih X hle H K hH hK iH iK
    · have hXcard : Nat.card X = n + 1 :=
        le_antisymm hcard (Nat.succ_le_of_lt (not_le.mp hle))
      by_cases hHbot : H = ⊥
      · rw [hHbot, bot_sup_eq]; exact iK
      · by_cases hKbot : K = ⊥
        · rw [hKbot, sup_bot_eq]; exact iH
        · haveI hHnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHbot
          haveI hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKbot
          haveI iHi : Group.IsNilpotent ↥H := iH
          haveI iKi : Group.IsNilpotent ↥K := iK
          haveI hZHn : (subCenter H).Normal := subCenter_normal hH
          haveI hZKn : (subCenter K).Normal := subCenter_normal hK
          have hcardH : Nat.card (X ⧸ subCenter H) ≤ n := by
            have hlt : Nat.card (X ⧸ subCenter H) < Nat.card X := by
              rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (subCenter H)]
              have h2 : 1 < Nat.card ↥(subCenter H) :=
                (Subgroup.one_lt_card_iff_ne_bot _).mpr (subCenter_ne_bot (H := H))
              simpa using Nat.mul_lt_mul_of_pos_left h2 (Nat.card_pos (α := X ⧸ subCenter H))
            rw [hXcard] at hlt
            exact Nat.lt_succ_iff.mp hlt
          have ihQH : Group.IsNilpotent ↥((H.map (QuotientGroup.mk' (subCenter H))) ⊔
              (K.map (QuotientGroup.mk' (subCenter H)))) :=
            ih (X ⧸ subCenter H) hcardH _ _
              (hH.map _ (QuotientGroup.mk'_surjective _)) (hK.map _ (QuotientGroup.mk'_surjective _))
              (isNilpotent_map _ iH) (isNilpotent_map _ iK)
          obtain ⟨m, hm⟩ := exists_lcs_le_of_quotient_nilpotent H K (subCenter H) ihQH
          have hcardK : Nat.card (X ⧸ subCenter K) ≤ n := by
            have hlt : Nat.card (X ⧸ subCenter K) < Nat.card X := by
              rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (subCenter K)]
              have h2 : 1 < Nat.card ↥(subCenter K) :=
                (Subgroup.one_lt_card_iff_ne_bot _).mpr (subCenter_ne_bot (H := K))
              simpa using Nat.mul_lt_mul_of_pos_left h2 (Nat.card_pos (α := X ⧸ subCenter K))
            rw [hXcard] at hlt
            exact Nat.lt_succ_iff.mp hlt
          have ihQK : Group.IsNilpotent ↥((H.map (QuotientGroup.mk' (subCenter K))) ⊔
              (K.map (QuotientGroup.mk' (subCenter K)))) :=
            ih (X ⧸ subCenter K) hcardK _ _
              (hH.map _ (QuotientGroup.mk'_surjective _)) (hK.map _ (QuotientGroup.mk'_surjective _))
              (isNilpotent_map _ iH) (isNilpotent_map _ iK)
          obtain ⟨m', hm'⟩ := exists_lcs_le_of_quotient_nilpotent H K (subCenter K) ihQK
          haveI : (subCenter H ⊓ subCenter K).Normal := inferInstance
          have hcom : ⁅subCenter H ⊓ subCenter K, H ⊔ K⁆ = ⊥ := by
            rw [Subgroup.commutator_sup_left,
              Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
                (le_trans inf_le_left (subCenter_le_centralizer H)),
              Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
                (le_trans inf_le_right (subCenter_le_centralizer K))]
            simp
          have hZcent : subCenter H ⊓ subCenter K ≤ Subgroup.centralizer (↑(H ⊔ K) : Set X) :=
            Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
          refine (Subgroup.isNilpotent_iff_lowerCentralSeries _).mpr ⟨max m m' + 1, ?_⟩
          rw [Subgroup.lowerCentralSeries_succ]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_trans
            (le_inf
              (le_trans (Subgroup.lowerCentralSeries_antitone (H ⊔ K) (le_max_left m m')) hm)
              (le_trans (Subgroup.lowerCentralSeries_antitone (H ⊔ K) (le_max_right m m')) hm'))
            hZcent)

/-- **Fitting's theorem** (finite case), direct form. -/
theorem nilpotent_sup_of_normal_finite {X : Type*} [Group X] [Finite X] (H K : Subgroup X)
    [H.Normal] [K.Normal] [Group.IsNilpotent ↥H] [Group.IsNilpotent ↥K] :
    Group.IsNilpotent ↥(H ⊔ K) :=
  pair_aux (Nat.card X) X le_rfl H K inferInstance inferInstance inferInstance inferInstance

/-- The `sSup` of a set of subgroups of a finite group that is closed under binary joins
and contains `⊥` is again a member of the set. -/
theorem sSup_mem_of_sup_closed {G : Type*} [Group G] [Finite G] {S : Set (Subgroup G)}
    (hbot : ⊥ ∈ S) (hsup : ∀ N ∈ S, ∀ M ∈ S, N ⊔ M ∈ S) : sSup S ∈ S := by
  have hfin : S.Finite := Set.toFinite S
  set F := hfin.toFinset with hF
  have hcoe : (F : Set (Subgroup G)) = S := hfin.coe_toFinset
  have key : ∀ T : Finset (Subgroup G), (∀ N ∈ T, N ∈ S) → T.sup id ∈ S := by
    intro T
    induction T using Finset.induction with
    | empty => intro _; simpa using hbot
    | insert a T ha ih =>
      intro h
      rw [Finset.sup_insert]
      exact hsup a (h a (Finset.mem_insert_self a T)) _
        (ih (fun N hN => h N (Finset.mem_insert_of_mem hN)))
  have heq : sSup S = F.sup id := by
    refine le_antisymm ?_ ?_
    · refine sSup_le fun N hN => ?_
      rw [← hcoe] at hN
      exact Finset.le_sup (f := id) hN
    · refine Finset.sup_le fun N hN => ?_
      exact le_sSup (by rw [← hcoe]; exact hN)
  rw [heq]
  exact key F (fun N hN => by rw [← hcoe]; exact hN)

/-- The set of normal nilpotent subgroups is closed under binary joins. -/
theorem mem_fittingSet_sup {G : Type*} [Group G] [Finite G] {N M : Subgroup G}
    (hN : N ∈ fittingSet G) (hM : M ∈ fittingSet G) : N ⊔ M ∈ fittingSet G := by
  obtain ⟨hn, hnil⟩ := hN
  obtain ⟨hm, hnil2⟩ := hM
  haveI := hn
  haveI := hm
  haveI := hnil
  haveI := hnil2
  exact ⟨inferInstance, nilpotent_sup_of_normal_finite N M⟩

theorem fitting_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent ↥(Work.Fitting.fitting G) := by
  have hmem : sSup (fittingSet G) ∈ fittingSet G :=
    sSup_mem_of_sup_closed (S := fittingSet G)
      ⟨inferInstance, inferInstance⟩
      (fun N hN M hM => mem_fittingSet_sup hN hM)
  exact hmem.2

end Work.Fitting
