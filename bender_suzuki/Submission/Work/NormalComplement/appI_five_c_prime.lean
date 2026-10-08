import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_five_a
import Submission.Work.NormalComplement.appI_two
import Submission.Work.NormalComplement.appI_five_c_aux
import Submission.Work.Coprime.All
import Submission.Work.Frobenius.Complement.sylow_isCyclic_of_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ### Elementary group-theoretic helpers -/

/-- The normalizer of an intersection contains the intersection of the normalizers. -/
lemma mem_normalizer_inf {u : G} {A B : Subgroup G}
    (hA : u ∈ Subgroup.normalizer (A : Set G)) (hB : u ∈ Subgroup.normalizer (B : Set G)) :
    u ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩,
    fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

/-- If `a` and `b` commute then so do `a⁻¹` and `b`. -/
lemma inv_mul_eq_of_comm {a b : G} (h : a * b = b * a) : a⁻¹ * b = b * a⁻¹ := by
  calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
    _ = a⁻¹ * (a * b) * a⁻¹ := by rw [← h]
    _ = b * a⁻¹ := by group

/-- If `a` and `b` commute then `a b a⁻¹ = b`. -/
lemma conj_eq_of_comm {a b : G} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  calc a * b * a⁻¹ = (b * a) * a⁻¹ := by rw [← h]
    _ = b := by group

/-- If `a` and `b` commute then `a b⁻¹ a⁻¹ = b⁻¹`. -/
lemma conj_inv_eq_of_comm {a b : G} (h : a * b = b * a) : a * b⁻¹ * a⁻¹ = b⁻¹ := by
  have h2 : b⁻¹ * a = a * b⁻¹ := inv_mul_eq_of_comm h.symm
  calc a * b⁻¹ * a⁻¹ = (b⁻¹ * a) * a⁻¹ := by rw [h2]
    _ = b⁻¹ := by group

/-- `V = C_X(t)` normalises itself. -/
lemma fixX_le_normalizer {t : G} {X : Subgroup G} :
    fixX t X ≤ Subgroup.normalizer ((fixX t X : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_iff.mpr (fun u hu v hv => by
    have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp hu.1
    have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hv.1
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      X.mul_mem (X.mul_mem hu.2 hv.2) (X.inv_mem hu.2)⟩
    calc u * v * u⁻¹ * t = u * v * (u⁻¹ * t) := by group
      _ = u * v * (t * u⁻¹) := by rw [inv_mul_eq_of_comm hut]
      _ = u * (v * t) * u⁻¹ := by group
      _ = u * (t * v) * u⁻¹ := by rw [hvt]
      _ = (u * t) * v * u⁻¹ := by group
      _ = (t * u) * v * u⁻¹ := by rw [hut]
      _ = t * (u * v * u⁻¹) := by group)

/-- `[t, x] = t⁻¹x⁻¹tx` is unchanged when `x` is multiplied on the left by an element of
`C(t)`. -/
lemma kappArg_mul_left {t d z : G} (hd : d * t = t * d) :
    t⁻¹ * (d * z)⁻¹ * t * (d * z) = t⁻¹ * z⁻¹ * t * z := by
  rw [mul_inv_rev]
  have h : d⁻¹ * t = t * d⁻¹ := inv_mul_eq_of_comm hd
  calc t⁻¹ * (z⁻¹ * d⁻¹) * t * (d * z) = t⁻¹ * z⁻¹ * (d⁻¹ * t) * d * z := by group
    _ = t⁻¹ * z⁻¹ * (t * d⁻¹) * d * z := by rw [h]
    _ = t⁻¹ * z⁻¹ * t * z := by group

/-- Conjugating `[t,z]` by an element `u` commuting with `t` gives `[t, uzu⁻¹]`. -/
lemma conj_kapp_eq {t u z : G} (hu : u * t = t * u) :
    u * (t⁻¹ * z⁻¹ * t * z) * u⁻¹ =
      t⁻¹ * (u * z * u⁻¹)⁻¹ * t * (u * z * u⁻¹) := by
  have h1 : u * t⁻¹ * u⁻¹ = t⁻¹ := conj_inv_eq_of_comm hu
  have h2 : u * t * u⁻¹ = t := conj_eq_of_comm hu
  have h3 : u * z⁻¹ * u⁻¹ = (u * z * u⁻¹)⁻¹ := by rw [mul_inv_rev]; group
  calc u * (t⁻¹ * z⁻¹ * t * z) * u⁻¹
      = (u * t⁻¹ * u⁻¹) * (u * z⁻¹ * u⁻¹) * (u * t * u⁻¹) * (u * z * u⁻¹) := by group
    _ = t⁻¹ * (u * z * u⁻¹)⁻¹ * t * (u * z * u⁻¹) := by rw [h1, h3, h2]

/-- `(toMulAut A M) a m = a • m` for a multiplicative action of a group on a monoid. -/
lemma toMulAut_apply_apply {A M : Type*} [Group A] [Monoid M] [MulDistribMulAction A M]
    (a : A) (m : M) : (MulDistribMulAction.toMulAut A M) a m = a • m := by
  rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]

/-! ### The abstract input: an odd `p`-group acting fixed-point-freely is cyclic -/

/-- A finite `p`-group of odd order which acts fixed-point-freely on a nontrivial finite group is
cyclic (Huppert V.8.7: an odd `p`-group Frobenius complement is cyclic). -/
theorem fpf_pgroup_isCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) {N : Type*} [Group N] [Finite N] [Nontrivial N]
    (ρ : P →* MulAut N) (hfpf : ∀ a : P, a ≠ 1 → ∀ n : N, ρ a n = n → n = 1) :
    IsCyclic P := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup hp hp2 hP ?_
  rintro Q ⟨e⟩
  have hQp : IsPGroup p Q := hP.to_subgroup Q
  haveI : IsMulCommutative Q := by
    rw [isMulCommutative_iff]
    intro a b
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hcyc : IsCyclic Q :=
    Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hp hQp (ρ.comp Q.subtype)
      (fun q hq n hn => hfpf (q : P) (fun h => hq (Subtype.ext h)) n hn)
  exact Work.Frobenius.Complement.not_isCyclic_multiplicative_zmod_prod hp
    ((MulEquiv.isCyclic e).mp hcyc)

/-! ### Appendix I (5)(c): the Sylow `q`-subgroup of `⟨K⟩` -/

/-- **Peterfalvi I, Appendix I (5)(c), the Sylow input.** If `U ≤ V = C_X(t)` is a nontrivial
`p`-subgroup acting fixed-point-freely on `K = Kapp t X` with `2 ≤ |K|`, then there is a prime
`q ∣ |K|` and a `U`-invariant Sylow `q`-subgroup `Q` of `⟨K⟩` which is not contained in `V`. -/
theorem appI_five_c_sylow {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime)
    {t : G} (ht : orderOf t = d) {X : Subgroup G} (htX : NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X) {p : ℕ} (hp : p.Prime)
    {U : Subgroup G} (hU : U ≤ fixX t X) (hUp : IsPGroup p U) (hU1 : U ≠ ⊥)
    (hK2 : 2 ≤ (Kapp t X).ncard)
    (hfpf : ∀ u ∈ U, u ≠ 1 → ∀ k ∈ Kapp t X, u * k * u⁻¹ = k → k = 1) :
    ∃ q : ℕ, ∃ Q : Subgroup G, q.Prime ∧ q ∣ (Kapp t X).ncard ∧ IsPGroup q Q ∧
      Q ≤ closureKapp t X ∧ ¬ q ∣ (Q.subgroupOf (closureKapp t X)).index ∧
      (∀ u ∈ U, Q.map (MulAut.conj u).toMonoidHom = Q) ∧ ¬ Q ≤ fixX t X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKX, hVnormK, hXnormKl, hsup, htKl, hKappKl, hcard⟩ := appI_four hd ht htX hdX
  have hfix := kapp_fixed_eq_one_of_fpf hU1 hfpf
  have hpKl : ¬ p ∣ Nat.card ↥(closureKapp t X) :=
    not_dvd_card_closureKapp hp hd ht htX hdX hsolv hU hUp hfix
  -- a prime `q` dividing `|K|`
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : (Kapp t X).ncard ≠ 1)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqKl : q ∣ Nat.card ↥(closureKapp t X) :=
    (appI_five_a hd ht htX hdX hsolv q hq).mpr hqdvd
  -- `U` acts coprimely on `⟨K⟩`
  have hUNKl : U ≤ Subgroup.normalizer ((closureKapp t X : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun u hu k hk => hXnormKl u (fixX_le_X (hU hu)) k hk)
  haveI hNor : FT.Normalizes U (closureKapp t X) := ⟨hUNKl⟩
  have hcop : (Nat.card ↥U).Coprime (Nat.card ↥(closureKapp t X)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hUp
    rw [hn]
    exact Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr hpKl)
  have hsolU : Group.IsSolvable ↥U := by
    haveI : Group.IsNilpotent ↥U := hUp.isNilpotent
    exact IsNilpotent.to_isSolvable
  obtain ⟨S, hS⟩ := Work.Coprime.exists_invariant_sylow U (G := ↥(closureKapp t X)) hcop
    (Or.inl hsolU) q
  let Q : Subgroup G := Subgroup.map (closureKapp t X).subtype (S : Subgroup ↥(closureKapp t X))
  have hQp : IsPGroup q Q := IsPGroup.map S.isPGroup' (closureKapp t X).subtype
  have hQle : Q ≤ closureKapp t X := Subgroup.map_subtype_le _
  have hQindex : ¬ q ∣ (Q.subgroupOf (closureKapp t X)).index :=
    (sylow_toSubgroup_isSylowIn S).2.2
  have hQinv : ∀ u ∈ U, Q.map (MulAut.conj u).toMonoidHom = Q := fun u hu =>
    map_conj_eq_of_normalizedBy (normalizedBy_map_subtype_of_invariant S hS ⟨u, hu⟩)
  -- `Q ⊄ V`
  have hQnotV : ¬ Q ≤ fixX t X := by
    intro hle
    have hle' : Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ closureKapp t X :=
      le_inf (fun x hx => (Subgroup.mem_inf.mp (hle hx)).1) hQle
    have hmono : Q.subgroupOf (closureKapp t X) ≤
        (Subgroup.centralizer ({t} : Set G) ⊓ closureKapp t X).subgroupOf (closureKapp t X) :=
      Subgroup.subgroupOf_mono _ hle'
    have hdvd := Subgroup.index_dvd_of_le hmono
    have hidx : ((Subgroup.centralizer ({t} : Set G) ⊓ closureKapp t X).subgroupOf
        (closureKapp t X)).index = (Kapp t X).ncard := by
      rw [← hKappKl]; exact (appI_kapp_ncard t (closureKapp t X)).symm
    have hqidx : q ∣ ((Subgroup.centralizer ({t} : Set G) ⊓ closureKapp t X).subgroupOf
        (closureKapp t X)).index := by rw [hidx]; exact hqdvd
    exact hQindex (hqidx.trans hdvd)
  exact ⟨q, Q, hq, hqdvd, hQp, hQle, hQindex, hQinv, hQnotV⟩

/-! ### Appendix I (5)(c): the fixed-point-free action on `N_Q(V ∩ Q)/(V ∩ Q)` -/

/-- **Peterfalvi I, Appendix I (5)(c), the quotient.** With `Q` a `U`-invariant `q`-subgroup of
`⟨K⟩` not contained in `V`, the group `N_Q(V ∩ Q)/(V ∩ Q)` is nontrivial and `U` acts on it
fixed-point-freely. -/
theorem appI_five_c_quotient {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime)
    {t : G} (ht : orderOf t = d) {X : Subgroup G} (htX : NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X) {p : ℕ} (hp : p.Prime)
    {U : Subgroup G} (hU : U ≤ fixX t X) (hUp : IsPGroup p U) (hU1 : U ≠ ⊥)
    (hfpf : ∀ u ∈ U, u ≠ 1 → ∀ k ∈ Kapp t X, u * k * u⁻¹ = k → k = 1)
    {q : ℕ} (hq : q.Prime) {Q : Subgroup G} (hQle : Q ≤ closureKapp t X) (hQp : IsPGroup q Q)
    (hQinv : ∀ u ∈ U, Q.map (MulAut.conj u).toMonoidHom = Q) (hQnotV : ¬ Q ≤ fixX t X) :
    Nontrivial (↥(normInQ (fixX t X) Q) ⧸ infSubOfNorm (fixX t X) Q) ∧
      ∃ ρ : U →* MulAut (↥(normInQ (fixX t X) Q) ⧸ infSubOfNorm (fixX t X) Q),
        ∀ u : U, u ≠ 1 → ∀ x, ρ u x = x → x = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hKX, hVnormK, hXnormKl, hsup, htKl, hKappKl, hcard⟩ := appI_four hd ht htX hdX
  -- `U` normalises `V`, `Q` and `W = V ⊓ Q`, hence `N_Q(W)`
  have hUNV : U ≤ Subgroup.normalizer ((fixX t X : Subgroup G) : Set G) :=
    fun u hu => fixX_le_normalizer (hU hu)
  have hUNQ : U ≤ Subgroup.normalizer (Q : Set G) := fun u hu =>
    mem_normalizer_of_normalizedBy (fun x hx => by
      have hm : u * x * u⁻¹ ∈ Q.map (MulAut.conj u).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        simp [MulAut.conj_apply]
      rwa [hQinv u hu] at hm)
  have hUNW : U ≤ Subgroup.normalizer ((fixX t X ⊓ Q : Subgroup G) : Set G) :=
    fun u hu => mem_normalizer_inf (hUNV hu) (hUNQ hu)
  haveI hNor : FT.Normalizes U (normInQ (fixX t X) Q) :=
    ⟨fun u hu => mem_normalizer_inf
      (Subgroup.le_normalizer (H := Subgroup.normalizer ((fixX t X ⊓ Q : Subgroup G) : Set G))
        (hUNW hu)) (hUNQ hu)⟩
  haveI hInv : FT.IsInvariant U (infSubOfNorm (fixX t X) Q) := by
    refine ⟨fun u => ?_⟩
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, FT.conj_smul_coe, Subgroup.coe_inv, inv_inv]
    exact (Subgroup.mem_normalizer_iff''.mp (hUNW u.2) x.1).symm
  refine ⟨?_, ⟨MulDistribMulAction.toMulAut U
    (↥(normInQ (fixX t X) Q) ⧸ infSubOfNorm (fixX t X) Q), ?_⟩⟩
  · rw [QuotientGroup.nontrivial_iff]
    intro htop
    have hle : normInQ (fixX t X) Q ≤ fixX t X ⊓ Q := Subgroup.subgroupOf_eq_top.mp htop
    have hWlt : fixX t X ⊓ Q < Q := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      exact hQnotV (le_trans (le_of_eq heq.symm) inf_le_left)
    have hlt : fixX t X ⊓ Q < normInQ (fixX t X) Q := by
      simpa [normInQ, inf_comm] using Work.Coprime.lt_inf_normalizer_of_lt hQp hWlt
    exact absurd hle (not_le_of_gt hlt)
  · intro u hu1 x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (infSubOfNorm (fixX t X) Q) x
    rw [toMulAut_apply_apply, QuotientGroup.mk'_apply, FT.quotient_smul_mk] at hx
    -- `hx : ↑(u • y) = ↑y`, hence `e := ↑((u • y)⁻¹ * y) ∈ V ⊓ Q`
    have he : (u • y)⁻¹ * y ∈ infSubOfNorm (fixX t X) Q := QuotientGroup.eq.mp hx
    have he_mem : (↑((u • y)⁻¹ * y) : G) ∈ fixX t X ⊓ Q := Subgroup.mem_subgroupOf.mp he
    set xG : G := (↑y : G) with hxG
    set e : G := (↑((u • y)⁻¹ * y) : G) with hedef
    -- the "left" commutator `d = u xG u⁻¹ xG⁻¹` lies in `V ⊓ Q`
    have hd_mem : xG * e⁻¹ * xG⁻¹ ∈ fixX t X ⊓ Q :=
      (Subgroup.mem_normalizer_iff.mp y.2.1 e⁻¹).mp ((fixX t X ⊓ Q).inv_mem he_mem)
    have hdeq : xG * e⁻¹ * xG⁻¹ = u.1 * xG * u.1⁻¹ * xG⁻¹ := by
      rw [hedef, hxG]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [FT.conj_smul_coe U (normInQ (fixX t X) Q) u y]
      group
    have hd : u.1 * xG * u.1⁻¹ * xG⁻¹ ∈ fixX t X ⊓ Q := hdeq ▸ hd_mem
    -- `k = [t, xG] ∈ K` and `u` fixes `k`
    have hxGKl : xG ∈ closureKapp t X := hQle y.2.2
    have hkK : t⁻¹ * xG⁻¹ * t * xG ∈ Kapp t X := by
      have h : t⁻¹ * xG⁻¹ * t * xG ∈ Kapp t (closureKapp t X) := ⟨xG, hxGKl, rfl⟩
      rwa [hKappKl] at h
    have hufix : u.1 * (t⁻¹ * xG⁻¹ * t * xG) * u.1⁻¹ = t⁻¹ * xG⁻¹ * t * xG := by
      have hut : u.1 * t = t * u.1 := Subgroup.mem_centralizer_singleton_iff.mp (hU u.2).1
      have hdC : (u.1 * xG * u.1⁻¹ * xG⁻¹) * t = t * (u.1 * xG * u.1⁻¹ * xG⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hd).1).1
      have hux : u.1 * xG * u.1⁻¹ = (u.1 * xG * u.1⁻¹ * xG⁻¹) * xG := by group
      rw [conj_kapp_eq hut, hux]
      exact kappArg_mul_left hdC
    have hk1 : t⁻¹ * xG⁻¹ * t * xG = 1 :=
      hfpf u.1 u.2 (fun h => hu1 (Subtype.ext h)) _ hkK hufix
    -- hence `xG` is centralised by `t`, so `y ∈ V ⊓ Q`
    have hxGt : xG * t = t * xG := by
      have h5 : t⁻¹ * xG⁻¹ * t = xG⁻¹ :=
        mul_right_cancel (show (t⁻¹ * xG⁻¹ * t) * xG = xG⁻¹ * xG by
          rw [show (t⁻¹ * xG⁻¹ * t) * xG = 1 from hk1, inv_mul_cancel])
      have h6 : t⁻¹ * xG * t = xG := by
        have := congrArg Inv.inv h5
        simpa [mul_inv_rev, inv_inv, mul_assoc] using this
      have := congrArg (fun w => t * w) h6
      simpa [mul_assoc] using this
    have hyW : y ∈ infSubOfNorm (fixX t X) Q := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxGt,
            (Subgroup.closure_le X).mpr hKX hxGKl⟩, y.2.2⟩
    have h1 : (QuotientGroup.mk' (infSubOfNorm (fixX t X) Q) y) =
        QuotientGroup.mk' (infSubOfNorm (fixX t X) Q) 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa using (infSubOfNorm (fixX t X) Q).inv_mem hyW
    simpa using h1

/-- **Peterfalvi I Appendix I (5)(c)** (p.201), with the missing hypothesis `p.Prime` restored and
the binder order of the first hypothesis fixed (the version without these is false — see
the counterexample documented in `Submission/Work/NormalComplement/appI_five_c.lean`).

`U` is a `p`-subgroup of `V = C_X(t)`:
* if `C_K(U) = 1` (every `k ∈ K` commuting with all of `U` is trivial) then `N_X(U) ⊆ V`;
* if `U` acts fixed-point-freely on `K = {[t,x] | x ∈ X}` then `U` is cyclic or generalised
  quaternion — hence cyclic when `|U|` is odd. -/
theorem appI_five_c_prime {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) (hsolv : Group.IsSolvable X) {p : ℕ} (hp : p.Prime)
    {U : Subgroup G} (hU : U ≤ Subgroup.centralizer ({t} : Set G) ⊓ X) (hUp : IsPGroup p U) :
    ((∀ k ∈ Work.NormalComplement.Kapp t X, (∀ u ∈ U, u * k * u⁻¹ = k) → k = 1) →
        ∀ z ∈ X, (∀ u ∈ U, z * u * z⁻¹ ∈ U) →
          z ∈ Subgroup.centralizer ({t} : Set G) ⊓ X) ∧
      (U ≠ ⊥ → 2 ≤ (Work.NormalComplement.Kapp t X).ncard →
        (∀ u ∈ U, u ≠ 1 → ∀ k ∈ Work.NormalComplement.Kapp t X,
          u * k * u⁻¹ = k → k = 1) →
        Odd (Nat.card U) → IsCyclic U) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_⟩
  · intro hCK
    exact mem_fixX_of_normalizes hd ht htX hdX hsolv hp hU hUp hCK
  · intro hU1 hK2 hfpf hodd
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hUp
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hU1 (Subgroup.card_eq_one.mp hn)
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr (by rw [hn]; exact dvd_pow_self 2 hn0))
    obtain ⟨q, Q, hq, hqdvd, hQp, hQle, hQindex, hQinv, hQnotV⟩ :=
      appI_five_c_sylow hd ht htX hdX hsolv hp hU hUp hU1 hK2 hfpf
    obtain ⟨hnt, ρ, hfpfρ⟩ :=
      appI_five_c_quotient hd ht htX hdX hsolv hp hU hUp hU1 hfpf hq hQle hQp hQinv hQnotV
    haveI : Nontrivial (↥(normInQ (fixX t X) Q) ⧸ infSubOfNorm (fixX t X) Q) := hnt
    exact fpf_pgroup_isCyclic hp hp2 hUp ρ hfpfρ

end Work.NormalComplement
