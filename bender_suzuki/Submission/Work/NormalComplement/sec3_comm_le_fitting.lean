/-
# `E' ∩ V ≤ F(E ∩ V)` — Ch. III §3 Prop. 1, step 4 (p. 177)

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. III §3 Prop. 1 step 4 concludes, in the notation
of the source (`E = W ∩ D`, `V = C_D(t)`, `F` the Fitting subgroup):

> By Fitting, `(E ∩ V)/F(E ∩ V)` embeds in `Aut F(E ∩ V)`, so it is abelian. Hence
> `[V ∩ E, V ∩ E] ⊆ F(E ∩ V)`.

and, using `E = K(V ∩ E)`, `K ⊆ E'`, `K ⊴ E` (Ch. III §2 Lemma 1) and `K ∩ V = 1`, that
`E' ∩ V = [V ∩ E, V ∩ E]`.  The present lemma records the consequence needed downstream:

  `E' ∩ V ≤ F(E ∩ V)`,

i.e. `Design.Ecomm H t W ⊓ centD H t ≤ Design.fitSub (Design.Egrp H t W ⊓ centD H t)`, under the
standing data `Setup3`, a `K`-complement `D = K ⋊ V` (`hKnc`) whose `K` is the set of elements of
`D` inverted by `t` (`hK`), and the cyclicity hypothesis `F(E ∩ V)` cyclic (`hcyc`, the conclusion
of step 3, `Work.NormalComplement.sec3_fitting_cyclic`).

The route formalised here:

* `E' ∩ V ≤ ⁅E ∩ V, E ∩ V⁆`.  Since `D = K ⊔ V` with `K ⊴ D` and `t` inverts `K` while fixing `V`,
  every `e ∈ E` can be written `e = b * k` with `b ∈ E ∩ V` and `k ∈ K`
  (`exists_mem_inf_mul_of_mem`, using `E^t = E` and `|K|` odd to deduce `k ∈ E`), so `E ≤ (E ∩ V) ⊔ K`;
  then the quotient `D/K ≅ V` (here: `Subgroup.map_le_map_iff` for `↥D →* ↥D ⧸ K.subgroupOf D`)
  shows `⁅E,E⁆ ≤ K ⊔ ⁅E ∩ V, E ∩ V⁆`, and `K ∩ V = ⊥` collapses the intersection with `V`.
* `⁅E ∩ V, E ∩ V⁆ ≤ F(E ∩ V)`, which is
  `Work.Fitting.commutator_le_fitting_of_isCyclic` applied to `B = E ∩ V` (solvable of odd order by
  Feit–Thompson, `F(B)` cyclic by `hcyc`).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.sec2_lemma1
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_fitting_le
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.commutator_le_fitting_of_isCyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.NormalComplement

/-! ## Auxiliary group theory -/

/-- In a group `K` of odd order, every element is a square: for `k ∈ K` and `n = |K|` odd,
`k = (k ^ 2) ^ ((n + 1) / 2)` (because `2 * ((n + 1) / 2) = n + 1` and `k ^ n = 1`). -/
theorem eq_pow_of_odd_card {G : Type*} [Group G] {K : Subgroup G} (hodd : Odd (Nat.card ↥K))
    {k : G} (hk : k ∈ K) : (k ^ 2) ^ ((Nat.card ↥K + 1) / 2) = k := by
  obtain ⟨s, hs⟩ := hodd
  have hkn : k ^ Nat.card ↥K = 1 := by
    have h : (⟨k, hk⟩ : ↥K) ^ Nat.card ↥K = 1 := pow_card_eq_one'
    have h2 := congrArg (Subtype.val) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  have hm : 2 * ((Nat.card ↥K + 1) / 2) = Nat.card ↥K + 1 := by omega
  calc (k ^ 2) ^ ((Nat.card ↥K + 1) / 2)
      = k ^ (2 * ((Nat.card ↥K + 1) / 2)) := by rw [pow_mul]
    _ = k ^ (Nat.card ↥K + 1) := by rw [hm]
    _ = k := by rw [pow_succ, hkn, one_mul]

/-- If `K ⊔ V = D` and `K ⊴ D` (here: `D ≤ N(K)` and `V ≤ D`), every element of `D` is a product
`v * k` with `v ∈ V`, `k ∈ K`: inside `↥D` the join is the set product (`Subgroup.normal_mul`),
and `K` is normal there (`Subgroup.normal_subgroupOf_of_le_normalizer`). -/
theorem exists_mul_of_mem_sup {G : Type*} [Group G] {D K V : Subgroup G}
    (hK : K ≤ D) (hV : V ≤ D) (hN : D ≤ Subgroup.normalizer (K : Set G))
    (hsup : K ⊔ V = D) :
    ∀ d ∈ D, ∃ v ∈ V, ∃ k ∈ K, d = v * k := by
  intro d hd
  haveI : (K.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have htop : (K.subgroupOf D) ⊔ (V.subgroupOf D) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK hV, hsup, Subgroup.subgroupOf_eq_top]
  have hmul : (((K.subgroupOf D) ⊔ (V.subgroupOf D) : Subgroup ↥D) : Set ↥D) =
      ((K.subgroupOf D : Set ↥D) * (V.subgroupOf D : Set ↥D)) :=
    Subgroup.normal_mul (K.subgroupOf D) (V.subgroupOf D)
  have hx : (⟨d, hd⟩ : ↥D) ∈
      (((K.subgroupOf D) ⊔ (V.subgroupOf D) : Subgroup ↥D) : Set ↥D) := by
    rw [htop]; exact Subgroup.mem_top _
  rw [hmul] at hx
  rw [Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  have haK : (a : G) ∈ K := ha
  have hbV : (b : G) ∈ V := hb
  have hab' : (a : G) * (b : G) = d := by
    have := congrArg (Subtype.val) hab
    simpa using this
  have hbN : (b : G) ∈ Subgroup.normalizer (K : Set G) := hN (hV hbV)
  exact ⟨(b : G), hbV, (b : G)⁻¹ * (a : G) * (b : G),
    (Subgroup.mem_normalizer_iff''.mp hbN (a : G)).mp haK,
    by rw [← hab']; group⟩

/-- **Step 4 of Ch. III §3 Prop. 1, group-theoretic part.**  `D = K ⋊ V` (`K ⊔ V = D`,
`K ∩ V = ⊥`, `K ⊴ D`), `t` inverts the elements of `K` and fixes those of `V` pointwise,
`E ≤ D` is `t`-invariant and `|K|` is odd.  Then every element of `E` factors as `b * k` with
`b ∈ E ∩ V` and `k ∈ K`.

For `e = v * k ∈ E` (possible by `exists_mul_of_mem_sup`) one has
`e⁻¹ * (t e t⁻¹) = k⁻² ∈ E ∩ K`, so `k = (k²)^((|K|+1)/2) ∈ E` (`eq_pow_of_odd_card`, `|K|` odd),
whence `v = e k⁻¹ ∈ E`. -/
theorem exists_mem_inf_mul_of_mem {G : Type*} [Group G] {D K V E : Subgroup G} {t : G}
    (hK : K ≤ D) (hV : V ≤ D) (hN : D ≤ Subgroup.normalizer (K : Set G))
    (hsup : K ⊔ V = D) (hkInv : ∀ k ∈ K, t * k * t⁻¹ = k⁻¹)
    (hVfix : ∀ v ∈ V, t * v * t⁻¹ = v)
    (hE : E ≤ D) (hEt : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hodd : Odd (Nat.card ↥K)) :
    ∀ e ∈ E, ∃ b ∈ E ⊓ V, ∃ k ∈ K, e = b * k := by
  intro e he
  obtain ⟨v, hvV, k, hkK, hve⟩ := exists_mul_of_mem_sup hK hV hN hsup e (hE he)
  have het : t * e * t⁻¹ = v * k⁻¹ := by
    have h1 : t * (v * k) * t⁻¹ = (t * v * t⁻¹) * (t * k * t⁻¹) := by group
    rw [hve, h1, hVfix v hvV, hkInv k hkK]
  have hkE : k ^ 2 ∈ E := by
    have hmem2 : e⁻¹ * (t * e * t⁻¹) ∈ E := mul_mem (inv_mem he) (hEt e he)
    have : e⁻¹ * (t * e * t⁻¹) = (k ^ 2)⁻¹ := by
      rw [het, hve]; group
    rw [this] at hmem2
    simpa using inv_mem hmem2
  have hkE' : k ∈ E := by
    have h := eq_pow_of_odd_card (K := K) hodd hkK
    rw [← h]
    exact pow_mem hkE _
  have hvE : v ∈ E := by
    have : e * k⁻¹ ∈ E := mul_mem he (inv_mem hkE')
    have h2 : e * k⁻¹ = v := by rw [hve]; group
    rwa [h2] at this
  exact ⟨v, ⟨hvE, hvV⟩, k, hkK, hve⟩

/-- The commutator subgroup of `X` sits inside `↥D` with the commutator subgroup of
`X.subgroupOf D`. -/
theorem subgroupOf_commutator_self {G : Type*} [Group G] {D X : Subgroup G} (hX : X ≤ D) :
    (⁅X,X⁆).subgroupOf D = ⁅X.subgroupOf D, X.subgroupOf D⁆ := by
  rw [← Subgroup.map_subtype_inj (H := D)]
  have h1 : Subgroup.map D.subtype ((⁅X,X⁆).subgroupOf D) = ⁅X,X⁆ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.commutator_le_of_le hX hX)]
  have h2 : Subgroup.map D.subtype (⁅X.subgroupOf D, X.subgroupOf D⁆) = ⁅X,X⁆ := by
    rw [Subgroup.map_commutator]
    simp only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX]
  rw [h1, h2]

/-- `D = K ⋊ V` (`K ⊔ V = D`, `K ◁ D`, `K ∩ V = ⊥`) and `W ≤ V`: then `(K ⊔ W) ∩ V = W`.
Every element of the join is a product `k * w` with `k ∈ K`, `w ∈ W ≤ V` (the join is the set
product in `↥D`), so an element lying in `V` has `k = x w⁻¹ ∈ K ∩ V = ⊥`. -/
theorem inf_sup_le_left_of_complement {G : Type*} [Group G] {D K V W : Subgroup G}
    (hWD : W ≤ D) (hWV : W ≤ V) (hKD : K ≤ D) (hVD : V ≤ D)
    (hN : D ≤ Subgroup.normalizer (K : Set G)) (hKV : K ⊓ V = ⊥) : (K ⊔ W) ⊓ V ≤ W := by
  intro x hx
  obtain ⟨hxKW, hxV⟩ := hx
  have hxD : x ∈ D := hVD hxV
  haveI : (K.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have htop : ((K ⊔ W).subgroupOf D) = K.subgroupOf D ⊔ W.subgroupOf D :=
    Subgroup.subgroupOf_sup hKD hWD
  have hx1 : (⟨x, hxD⟩ : ↥D) ∈
      (((K.subgroupOf D) ⊔ (W.subgroupOf D) : Subgroup ↥D) : Set ↥D) := by
    rw [← htop]; exact hxKW
  have hmul : (((K.subgroupOf D) ⊔ (W.subgroupOf D) : Subgroup ↥D) : Set ↥D) =
      ((K.subgroupOf D : Set ↥D) * (W.subgroupOf D : Set ↥D)) :=
    Subgroup.normal_mul _ _
  rw [hmul, Set.mem_mul] at hx1
  obtain ⟨a, ha, b, hb, hab⟩ := hx1
  have haK : (a : G) ∈ K := ha
  have hbW : (b : G) ∈ W := hb
  have hab' : (a : G) * (b : G) = x := by
    have := congrArg (Subtype.val) hab
    simpa using this
  have haV : (a : G) ∈ V := by
    have h1 : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
    rw [h1]
    exact mul_mem hxV (inv_mem (hWV hbW))
  have ha_bot : (a : G) ∈ (⊥ : Subgroup G) := by
    have : (a : G) ∈ K ⊓ V := ⟨haK, haV⟩
    rwa [hKV] at this
  have hai : (a : G) = 1 := by simpa using ha_bot
  have hxb : x = (b : G) := by rw [← hab', hai, one_mul]
  rw [hxb]
  exact hbW

/-- **Step 4 of Ch. III §3 Prop. 1, commutator form.**  `D = K ⋊ V`, `E ≤ D`, `B = E ∩ V` and
`E ≤ B ⊔ K`.  Then `E' ∩ V ≤ [B,B]`.

Indeed, `K ⊴ D` collapses the image of `E` in `D/K` to that of `B = E ∩ V` (using `E ≤ B ⊔ K`),
so `[E', E']` and `[B,B]` have the same image under `↥D →* ↥D ⧸ K.subgroupOf D`; by
`Subgroup.map_le_map_iff` this gives `E' ≤ [B,B] ⊔ K`, and `inf_sup_le_left_of_complement` with
`[B,B] ≤ B ≤ V` and `K ∩ V = ⊥` gives the result. -/
theorem comm_inf_le_of_le_sup {G : Type*} [Group G] {D K V E B : Subgroup G}
    (hB : B = E ⊓ V) (hE : E ≤ D) (hKD : K ≤ D) (hVD : V ≤ D)
    (hN : D ≤ Subgroup.normalizer (K : Set G)) (hKV : K ⊓ V = ⊥)
    (hEB : E ≤ B ⊔ K) : ⁅E,E⁆ ⊓ V ≤ ⁅B,B⁆ := by
  have hBD : B ≤ D := hB ▸ inf_le_right.trans hVD
  have hBE : B ≤ E := hB ▸ inf_le_left
  have hBV : B ≤ V := hB ▸ inf_le_right
  haveI : (K.subgroupOf D).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hmap : (E.subgroupOf D).map (QuotientGroup.mk' (K.subgroupOf D)) =
      (B.subgroupOf D).map (QuotientGroup.mk' (K.subgroupOf D)) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk']
      rw [← Subgroup.subgroupOf_sup hBD hKD]
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hEB hy
    · apply Subgroup.map_mono
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hBE hy
  have hcomm : (⁅E.subgroupOf D, E.subgroupOf D⁆).map (QuotientGroup.mk' (K.subgroupOf D)) =
      (⁅B.subgroupOf D, B.subgroupOf D⁆).map (QuotientGroup.mk' (K.subgroupOf D)) := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmap]
  have hle : ⁅E.subgroupOf D, E.subgroupOf D⁆ ≤
      ⁅B.subgroupOf D, B.subgroupOf D⁆ ⊔ K.subgroupOf D := by
    have h := (Subgroup.map_le_map_iff (f := QuotientGroup.mk' (K.subgroupOf D))).mp
      (le_of_eq hcomm)
    rwa [QuotientGroup.ker_mk'] at h
  intro x hx
  obtain ⟨hxE, hxV⟩ := hx
  have hxD : x ∈ D := hVD hxV
  have hx1 : (⟨x, hxD⟩ : ↥D) ∈ ⁅E.subgroupOf D, E.subgroupOf D⁆ := by
    rw [← subgroupOf_commutator_self hE]
    exact hxE
  have hx2 : (⟨x, hxD⟩ : ↥D) ∈ ⁅B.subgroupOf D, B.subgroupOf D⁆ ⊔ K.subgroupOf D := hle hx1
  have hsup' : ((⁅B,B⁆ ⊔ K).subgroupOf D) =
      ⁅B.subgroupOf D, B.subgroupOf D⁆ ⊔ K.subgroupOf D := by
    rw [Subgroup.subgroupOf_sup (Subgroup.commutator_le_of_le hBD hBD) hKD,
      subgroupOf_commutator_self hBD]
  have hx3 : x ∈ ⁅B,B⁆ ⊔ K := by
    rw [← hsup'] at hx2
    exact hx2
  have h4 := inf_sup_le_left_of_complement (D := D) (K := K) (V := V) (W := ⁅B,B⁆)
    (Subgroup.commutator_le_of_le hBD hBD) (Subgroup.commutator_le_of_le hBV hBV) hKD hVD hN hKV
  exact h4 ⟨by simpa [sup_comm] using hx3, hxV⟩

/-! ## The lemma -/

theorem sec3_comm_le_fitting (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (K : Subgroup G)
    (hK : (K : Set G) = Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t)
    (hKnc : Work.NormalComplement.IsNormalComplementOf K (Submission.Blueprint.centD H t)
      (Submission.Blueprint.twoPoint H t))
    (hcyc : IsCyclic ↥(Work.NormalComplement.Design.fitSub
      (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t))) :
    Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      Work.NormalComplement.Design.fitSub (Work.NormalComplement.Design.Egrp H t W ⊓
        Submission.Blueprint.centD H t) := by
  -- the data of the complement `D = K ⋊ V`
  have hKD : K ≤ Submission.Blueprint.twoPoint H t := hKnc.1
  have hN : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (K : Set G) := hKnc.2.1
  have hKV : K ⊓ Submission.Blueprint.centD H t = ⊥ := hKnc.2.2.1
  have hsup : K ⊔ Submission.Blueprint.centD H t = Submission.Blueprint.twoPoint H t :=
    hKnc.2.2.2
  have hVD : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t := inf_le_left
  have hED : Work.NormalComplement.Design.Egrp H t W ≤ Submission.Blueprint.twoPoint H t :=
    inf_le_right
  -- `|D|` (and hence `|K|`, `|E ∩ V|`) is odd
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
  have hoddK : Odd (Nat.card ↥K) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le hKD)
  -- `t` inverts `K` and fixes `V` pointwise
  have hKinv : ∀ k ∈ K, t * k * t⁻¹ = k⁻¹ := by
    intro k hk
    have hk' : k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := hK ▸ hk
    exact hk'.2
  have hVfix : ∀ v ∈ Submission.Blueprint.centD H t, t * v * t⁻¹ = v := by
    intro v hv
    have hcomm : v * t = t * v := (Subgroup.mem_centralizer_singleton_iff.mp hv.2)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- §2 Lemma 1: `K ⊆ E'` and `E` is `t`-invariant
  have hsec2 := sec2_lemma1 hFT h
  have hEt : ∀ e ∈ Work.NormalComplement.Design.Egrp H t W,
      t * e * t⁻¹ ∈ Work.NormalComplement.Design.Egrp H t W := hsec2.2.1
  -- the factorisation `E ≤ (E ∩ V) ⊔ K`
  have hdecomp := exists_mem_inf_mul_of_mem (D := Submission.Blueprint.twoPoint H t) (K := K)
    (V := Submission.Blueprint.centD H t) (E := Work.NormalComplement.Design.Egrp H t W)
    hKD hVD hN hsup hKinv hVfix hED hEt hoddK
  have hEB : Work.NormalComplement.Design.Egrp H t W ≤
      (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t) ⊔ K := by
    intro e he
    obtain ⟨b, hb, k, hk, hbek⟩ := hdecomp e he
    rw [hbek]
    exact mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hk)
  -- `E' ∩ V ≤ [E ∩ V, E ∩ V]`
  have hcrux : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      ⁅Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t,
        Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t⁆ :=
    comm_inf_le_of_le_sup (D := Submission.Blueprint.twoPoint H t) (K := K)
      (V := Submission.Blueprint.centD H t) (E := Work.NormalComplement.Design.Egrp H t W)
      (B := Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)
      rfl hED hKD hVD hN hKV hEB
  -- `[E ∩ V, E ∩ V] ≤ F(E ∩ V)` (cyclic Fitting subgroup, solvable by Feit–Thompson)
  have hoddB : Odd (Nat.card ↥(Work.NormalComplement.Design.Egrp H t W ⊓
      Submission.Blueprint.centD H t)) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le (inf_le_right.trans hVD))
  have hsol : Group.IsSolvable ↥(Work.NormalComplement.Design.Egrp H t W ⊓
      Submission.Blueprint.centD H t) := hFT _ hoddB
  exact hcrux.trans (Work.Fitting.commutator_le_fitting_of_isCyclic _ hsol hcyc)

end Work.NormalComplement
