import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite
import Submission.NK.TameStructure.ProCyclic.Defs
import Submission.NK.TameStructure.ProCyclic.exists_continuous_surjective_zhat_of_isProCyclic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace NK.TameStructure.ProCyclic

noncomputable section

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-! ## The `p`-part of the finite cyclic quotients `H ⧸ M`

Throughout, `H` is a compact totally disconnected topological group and `M` ranges over the open
normal subgroups of `H`.  For a fixed prime `p` we write

* `idx M` for the index `[H : M]` (the order of the finite group `H ⧸ M`),
* `vp p M` for the exponent of `p` in `idx M`,
* `up p M` for the prime-to-`p` part `idx M / p ^ vp p M` of `idx M`,
* `Cp p M` for the `p`-part of `H ⧸ M`, i.e. the kernel of the `p ^ vp p M`-th power map.
-/

/-- The index of an open normal subgroup. -/
abbrev idx (M : OpenNormalSubgroup H) : ℕ := M.toSubgroup.index

/-- The exponent of `p` in the index of `M`. -/
abbrev vp (p : ℕ) (M : OpenNormalSubgroup H) : ℕ := padicValNat p (idx M)

/-- The prime-to-`p` part of the index of `M`. -/
abbrev up (p : ℕ) (M : OpenNormalSubgroup H) : ℕ := idx M / p ^ vp p M

/-- The `k`-th power map on the quotient `H ⧸ M`, as a monoid homomorphism. -/
def powMap (M : OpenNormalSubgroup H) (k : ℕ) :
    (H ⧸ M.toSubgroup) →* (H ⧸ M.toSubgroup) :=
  powMonoidHom k

theorem powMap_apply (M : OpenNormalSubgroup H) (k : ℕ) (x : H ⧸ M.toSubgroup) :
    powMap M k x = x ^ k := rfl

/-- The `p`-part of the finite cyclic group `H ⧸ M`: the kernel of the `p ^ vp p M`-th power
map, i.e. the subgroup of elements whose order is a power of `p`. -/
def Cp (p : ℕ) (M : OpenNormalSubgroup H) : Subgroup (H ⧸ M.toSubgroup) :=
  (powMap M (p ^ vp p M)).ker

/-! ### Elementary facts about the index and its `p`-part -/

theorem finiteIndex_subgroup (M : OpenNormalSubgroup H) : M.toSubgroup.FiniteIndex :=
  M.toSubgroup.finiteIndex_of_finite_quotient

instance (M : OpenNormalSubgroup H) : Finite (H ⧸ M.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen M.toSubgroup M.toOpenSubgroup.isOpen'

theorem idx_ne_zero (M : OpenNormalSubgroup H) : idx M ≠ 0 :=
  (finiteIndex_subgroup M).index_ne_zero

theorem quot_card (M : OpenNormalSubgroup H) : Nat.card (H ⧸ M.toSubgroup) = idx M :=
  (Subgroup.index_eq_card M.toSubgroup).symm

theorem quot_isCyclic (hcyc : NK.LocalTame.IsProCyclic H) (M : OpenNormalSubgroup H) :
    IsCyclic (H ⧸ M.toSubgroup) :=
  hcyc M.toSubgroup (finiteIndex_subgroup M)

/-- In the finite group `H ⧸ M`, the `[H : M]`-th power of every element is `1`. -/
theorem pow_idx_eq_one (M : OpenNormalSubgroup H) (z : H ⧸ M.toSubgroup) : z ^ idx M = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← quot_card M]
  exact orderOf_dvd_natCard z

theorem pow_vp_dvd_idx {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H) :
    p ^ vp p M ∣ idx M := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (padicValNat_dvd_iff_le (a := idx M) (n := vp p M) (idx_ne_zero M)).mpr le_rfl

theorem up_mul_pow_vp {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H) :
    up p M * p ^ vp p M = idx M := by
  rw [up, Nat.div_mul_cancel (pow_vp_dvd_idx hp M)]

theorem up_dvd_idx {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H) : up p M ∣ idx M :=
  ⟨p ^ vp p M, (up_mul_pow_vp hp M).symm ▸ rfl⟩

theorem up_ne_zero {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H) : up p M ≠ 0 := by
  intro h
  have h1 := up_mul_pow_vp hp M
  rw [h, zero_mul] at h1
  exact idx_ne_zero M h1.symm

theorem coprime_up {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H) :
    Nat.Coprime (up p M) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdiv
  obtain ⟨t, ht⟩ := hdiv
  have h1 : p ^ (vp p M + 1) ∣ idx M := by
    rw [← up_mul_pow_vp hp M, ht, pow_succ]
    exact ⟨t, by ring⟩
  have h3 : vp p M + 1 ≤ vp p M :=
    (padicValNat_dvd_iff_le (a := idx M) (n := vp p M + 1) (idx_ne_zero M)).mp h1
  omega

theorem vp_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime) {M : OpenNormalSubgroup H}
    (h : ¬ p ∣ idx M) : vp p M = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact padicValNat.eq_zero_of_not_dvd h

theorem card_Cp {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H)
    [IsCyclic (H ⧸ M.toSubgroup)] : Nat.card (Cp p M) = p ^ vp p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ vp p M ∣ idx M := pow_vp_dvd_idx hp M
  have h1 : Nat.card (Cp p M) = Nat.card ↥((powMonoidHom (p ^ vp p M) :
      (H ⧸ M.toSubgroup) →* (H ⧸ M.toSubgroup)).ker) := rfl
  rw [h1, IsCyclic.card_powMonoidHom_ker (H ⧸ M.toSubgroup) (p ^ vp p M), quot_card M,
    Nat.gcd_eq_right hdvd]

/-- **The `p`-part of `H ⧸ M` is the image of the prime-to-`p`-th power map.** -/
theorem Cp_eq_range {p : ℕ} (hp : p.Prime) (M : OpenNormalSubgroup H)
    [IsCyclic (H ⧸ M.toSubgroup)] : Cp p M = (powMap M (up p M)).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ↥(powMap M (up p M)).range = p ^ vp p M := by
    have h1 : Nat.card ↥(powMap M (up p M)).range = Nat.card ↥((powMonoidHom (up p M) :
        (H ⧸ M.toSubgroup) →* (H ⧸ M.toSubgroup)).range) := rfl
    rw [h1, IsCyclic.card_powMonoidHom_range (H ⧸ M.toSubgroup) (up p M), quot_card M,
      Nat.gcd_eq_right (up_dvd_idx hp M),
      Nat.div_eq_iff_eq_mul_left (Nat.pos_of_ne_zero (up_ne_zero hp M)) (up_dvd_idx hp M),
      mul_comm, up_mul_pow_vp hp M]
  refine (Subgroup.eq_of_le_of_card_ge (K := Cp p M) ?_ ?_).symm
  · rintro y ⟨z, rfl⟩
    rw [Cp, MonoidHom.mem_ker, powMap_apply, powMap_apply, ← pow_mul, up_mul_pow_vp hp M]
    exact pow_idx_eq_one M z
  · rw [card_Cp hp M, hcard]


/-! ### Compatibility of the `p`-parts along `M ↦ M'`

If `M ≤ M'` then the natural surjection `H ⧸ M ↠ H ⧸ M'` carries the `p`-part of `H ⧸ M`
onto the `p`-part of `H ⧸ M'`.  This is the compatibility that makes the system of `p`-parts of
the finite quotients into a surjective inverse system whose limit is the `p`-part of `H`.
-/

/-- The relative index relation `[H : M] = [M' : M] · [H : M']` for `M ≤ M'`. -/
theorem mul_idx_eq (M M' : OpenNormalSubgroup H) (h : M.toSubgroup ≤ M'.toSubgroup) :
    M.toSubgroup.relIndex M'.toSubgroup * idx M' = idx M :=
  Subgroup.relIndex_mul_index h

theorem relIndex_ne_zero (M M' : OpenNormalSubgroup H) (h : M.toSubgroup ≤ M'.toSubgroup) :
    M.toSubgroup.relIndex M'.toSubgroup ≠ 0 := by
  intro h0
  have := mul_idx_eq M M' h
  rw [h0, zero_mul] at this
  exact idx_ne_zero M this.symm

/-- The prime-to-`p` part of the index of a subgroup of finite index is coprime to `p`. -/
theorem coprime_div_valuation {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (n / p ^ padicValNat p n) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p n with hv
  have hdvd0 : p ^ v ∣ n := by
    rw [hv]
    exact (padicValNat_dvd_iff_le (a := n) (n := padicValNat p n) hn).mpr le_rfl
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hdiv
  obtain ⟨t, ht⟩ := hdiv
  have h1 : p ^ (v + 1) ∣ n := by
    rw [← Nat.div_mul_cancel hdvd0, ht]
    refine ⟨t, ?_⟩
    rw [pow_succ]
    ring
  have h2 : ¬ p ^ (padicValNat p n + 1) ∣ n := pow_succ_padicValNat_not_dvd hn
  rw [hv] at h1
  exact h2 h1

theorem coprime_div_vp_of_le {p : ℕ} (hp : p.Prime) {M M' : OpenNormalSubgroup H}
    (h : M.toSubgroup ≤ M'.toSubgroup) :
    Nat.Coprime (M.toSubgroup.relIndex M'.toSubgroup /
      p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) p :=
  coprime_div_valuation hp (relIndex_ne_zero M M' h)

/-- `up p M = c * up p M'` for the prime-to-`p` part `c` of the relative index `[M' : M]`. -/
theorem up_eq_mul {p : ℕ} (hp : p.Prime) {M M' : OpenNormalSubgroup H}
    (h : M.toSubgroup ≤ M'.toSubgroup) :
    up p M = (M.toSubgroup.relIndex M'.toSubgroup /
      p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) * up p M' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht0 : M.toSubgroup.relIndex M'.toSubgroup ≠ 0 := relIndex_ne_zero M M' h
  have hd' : idx M' ≠ 0 := idx_ne_zero M'
  have hv : padicValNat p (idx M) =
      padicValNat p (M.toSubgroup.relIndex M'.toSubgroup) + padicValNat p (idx M') := by
    rw [← mul_idx_eq M M' h, padicValNat.mul ht0 hd']
  have hdvd1 : p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup) ∣
      M.toSubgroup.relIndex M'.toSubgroup :=
    (padicValNat_dvd_iff_le (a := M.toSubgroup.relIndex M'.toSubgroup)
      (n := padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) ht0).mpr le_rfl
  have hdvd2 : p ^ padicValNat p (idx M') ∣ idx M' :=
    (padicValNat_dvd_iff_le (a := idx M')
      (n := padicValNat p (idx M')) hd').mpr le_rfl
  rw [up, up, vp, vp, hv, ← mul_idx_eq M M' h, pow_add,
    ← Nat.div_mul_div_comm hdvd1 hdvd2]

theorem gcd_idx_up {p : ℕ} (hp : p.Prime) {M M' : OpenNormalSubgroup H}
    (h : M.toSubgroup ≤ M'.toSubgroup) : Nat.gcd (idx M') (up p M) = up p M' := by
  have hc := coprime_div_vp_of_le (p := p) hp h
  have hup := up_eq_mul (p := p) hp h
  have hd' := up_mul_pow_vp (p := p) hp M'
  have hgcd : Nat.gcd (p ^ vp p M')
      (M.toSubgroup.relIndex M'.toSubgroup /
        p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) = 1 :=
    Nat.Coprime.gcd_eq_one (hc.symm.pow_left (vp p M'))
  rw [hup, ← hd']
  rw [show (up p M' * p ^ vp p M').gcd
        ((M.toSubgroup.relIndex M'.toSubgroup /
          p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) * up p M')
      = up p M' * Nat.gcd (p ^ vp p M')
        (M.toSubgroup.relIndex M'.toSubgroup /
          p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup)) from by
    rw [mul_comm _ (up p M'), Nat.gcd_mul_left]]
  rw [hgcd, mul_one]

theorem dvd_idx_up_mul {p : ℕ} (hp : p.Prime) {M M' : OpenNormalSubgroup H}
    (h : M.toSubgroup ≤ M'.toSubgroup) : idx M' ∣ up p M * p ^ vp p M' := by
  have hup := up_eq_mul (p := p) hp h
  refine ⟨M.toSubgroup.relIndex M'.toSubgroup /
      p ^ padicValNat p (M.toSubgroup.relIndex M'.toSubgroup), ?_⟩
  rw [hup, mul_assoc, up_mul_pow_vp hp M', mul_comm]

/-- The `[H : M]`-th power of an element vanishes whenever `[H : M]` divides the exponent. -/
theorem pow_eq_one_of_idx_dvd (M : OpenNormalSubgroup H) (z : H ⧸ M.toSubgroup) {n : ℕ}
    (h : idx M ∣ n) : z ^ n = 1 :=
  (orderOf_dvd_iff_pow_eq_one).mp (dvd_trans (quot_card M ▸ orderOf_dvd_natCard z) h)

/-- **Compatibility of the `p`-parts.**  For `M ≤ M'` the natural map `H ⧸ M →* H ⧸ M'` carries
the `p`-part of `H ⧸ M` onto the `p`-part of `H ⧸ M'`. -/
theorem map_Cp_eq {p : ℕ} (hp : p.Prime) {M M' : OpenNormalSubgroup H}
    (h : M.toSubgroup ≤ M'.toSubgroup) [IsCyclic (H ⧸ M.toSubgroup)]
    [IsCyclic (H ⧸ M'.toSubgroup)] :
    (Cp p M).map (QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) h) = Cp p M' := by
  haveI : Fact p.Prime := ⟨hp⟩
  set φ := QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) h with hφ
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M'.toSubgroup y
    exact ⟨QuotientGroup.mk' M.toSubgroup x, QuotientGroup.map_mk' _ _ _ _ x⟩
  have hcard : Nat.card ↥(powMap M' (up p M)).range = p ^ vp p M' := by
    have h1 : Nat.card ↥(powMap M' (up p M)).range = Nat.card ↥((powMonoidHom (up p M) :
        (H ⧸ M'.toSubgroup) →* (H ⧸ M'.toSubgroup)).range) := rfl
    rw [h1, IsCyclic.card_powMonoidHom_range (H ⧸ M'.toSubgroup) (up p M), quot_card M',
      gcd_idx_up hp h,
      Nat.div_eq_iff_eq_mul_left (Nat.pos_of_ne_zero (up_ne_zero hp M')) (up_dvd_idx hp M'),
      mul_comm, up_mul_pow_vp hp M']
  have himg : (Cp p M).map φ = (powMap M' (up p M)).range := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      rw [Cp_eq_range hp M] at hz
      obtain ⟨w, rfl⟩ := hz
      exact ⟨φ w, by rw [powMap_apply, powMap_apply, map_pow]⟩
    · rintro y ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj w
      refine ⟨z ^ (up p M), ?_, by rw [powMap_apply, map_pow]⟩
      rw [Cp_eq_range hp M]
      exact ⟨z, rfl⟩
  rw [himg]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨z, rfl⟩
    rw [Cp, MonoidHom.mem_ker, powMap_apply, powMap_apply, ← pow_mul]
    exact pow_eq_one_of_idx_dvd M' z (dvd_idx_up_mul hp h)
  · rw [card_Cp hp M']
    exact le_of_eq hcard.symm

/-! ## The `p`-part of `H`

`pPart p` is the subgroup of elements whose image in every finite cyclic quotient `H ⧸ M` lies in
its `p`-part; `pCore p` is the intrinsic description of the same subgroup, as the intersection of
the images of the `m`-th power maps for `m` prime to `p`.  The two are proved equal
(`pPart_eq_pCore`), which exhibits `pCore p` as a characteristic subgroup and gives it a surjective
inverse system description.
-/

/-- The `p`-part of `H`, described through the finite quotients. -/
def pPart (p : ℕ) : Subgroup H :=
  ⨅ (M : OpenNormalSubgroup H), (Cp p M).comap (QuotientGroup.mk' M.toSubgroup)

/-- The `p`-part of `H`, described as the intersection of the prime-to-`p` power subgroups. -/
def pCore (p : ℕ) : Subgroup H :=
  ⨅ (m : {m : ℕ // Nat.Coprime m p}), (powMonoidHom (m : ℕ) : H →* H).range

theorem mem_pPart {p : ℕ} {x : H} :
    x ∈ pPart p ↔ ∀ M : OpenNormalSubgroup H, QuotientGroup.mk' M.toSubgroup x ∈ Cp p M :=
  Subgroup.mem_iInf

theorem mem_pCore {p : ℕ} {x : H} :
    x ∈ pCore p ↔ ∀ m : {m : ℕ // Nat.Coprime m p},
      x ∈ (powMonoidHom (m : ℕ) : H →* H).range :=
  Subgroup.mem_iInf

/-- An element of the `p`-part is, for every open normal `M`, the image of the prime-to-`p` part
of the index under the `(up p M)`-th power map. -/
theorem pCore_le_pPart {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H) :
    (pCore p : Subgroup H) ≤ pPart p := by
  intro x hx
  rw [mem_pPart]
  intro M
  haveI := quot_isCyclic hcyc M
  rw [Cp_eq_range hp M]
  rw [mem_pCore] at hx
  obtain ⟨z, hz⟩ : ∃ z : H, z ^ (up p M) = x := by
    have hmem : x ∈ (powMonoidHom (up p M) : H →* H).range :=
      hx ⟨up p M, coprime_up hp M⟩
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨z, by simpa only [powMonoidHom_apply] using hz⟩
  refine ⟨QuotientGroup.mk' M.toSubgroup z, ?_⟩
  rw [powMap_apply, ← map_pow, hz]


/-! ## Compactness along the open normal subgroups -/

/-- **A compactness principle.**  A family of closed subsets of `H` indexed by the open normal
subgroups, which is increasing along inclusions (`M ≤ M'` gives `T M ⊆ T M'`) and each member of
which is nonempty, has nonempty intersection. -/
theorem nonempty_iInter_of_openNormal (T : OpenNormalSubgroup H → Set H)
    (hclosed : ∀ M, IsClosed (T M)) (hne : ∀ M, (T M).Nonempty)
    (hmono : ∀ M M', M.toSubgroup ≤ M'.toSubgroup → T M ⊆ T M') :
    (⋂ M, T M).Nonempty := by
  refine CompactSpace.iInter_nonempty hclosed fun s => ?_
  rcases s.eq_empty_or_nonempty with rfl | hne'
  · exact ⟨1, by simp⟩
  · set M : OpenNormalSubgroup H := s.inf' hne' id with hM
    have hle : ∀ M' ∈ s, M.toSubgroup ≤ M'.toSubgroup := fun M' hM' => Finset.inf'_le id hM'
    refine ⟨(hne M).some, ?_⟩
    simp only [Set.mem_iInter]
    exact fun M' hM' => hmono M M' (hle M' hM') (hne M).some_mem

/-- In a finite group of order coprime to `k`, every element is a `k`-th power. -/
theorem pow_surjective_of_coprime_card {k : ℕ} {Q : Type*} [CommGroup Q] [Finite Q]
    (h : Nat.Coprime k (Nat.card Q)) : ∀ q : Q, ∃ w : Q, w ^ k = q := by
  have hinj : Function.Injective (fun w : Q => w ^ k) := by
    intro a b hab
    have hab' : a ^ k = b ^ k := hab
    have h1 : (a * b⁻¹) ^ k = 1 := by rw [mul_pow, hab', inv_pow, mul_inv_cancel]
    have h2 : orderOf (a * b⁻¹) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf (a * b⁻¹) ∣ Nat.card Q := orderOf_dvd_natCard _
    have h4 : orderOf (a * b⁻¹) = 1 :=
      Nat.dvd_one.mp (h.gcd_eq_one ▸ Nat.dvd_gcd h2 h3)
    exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp h4)
  intro q
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.mp hinj q
  exact ⟨w, hw⟩

/-- A finite commutative group in which every element is a `k`-th power has order coprime to `k`
(for `k` prime). -/
theorem coprime_card_of_pow_surjective {k : ℕ} (hk : k.Prime) {Q : Type*} [CommGroup Q] [Finite Q]
    (h : ∀ q : Q, ∃ w : Q, w ^ k = q) : Nat.Coprime k (Nat.card Q) := by
  haveI : Fact k.Prime := ⟨hk⟩
  have hrange : (powMonoidHom k : Q →* Q).range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro q
    obtain ⟨w, hw⟩ := h q
    exact MonoidHom.mem_range.mpr ⟨w, by simpa only [powMonoidHom_apply] using hw⟩
  have hker : (powMonoidHom k : Q →* Q).ker = ⊥ := by
    have h2 : Nat.card ↥(powMonoidHom k : Q →* Q).ker * Nat.card Q = Nat.card Q := by
      have h3 := Subgroup.card_mul_index (powMonoidHom k : Q →* Q).ker
      rw [Subgroup.index_ker, hrange] at h3
      simpa using h3
    haveI : Nonempty Q := ⟨1⟩
    have h1 : Nat.card ↥(powMonoidHom k : Q →* Q).ker = 1 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h2, one_mul])
    exact Subgroup.card_eq_one.mp h1
  rw [hk.coprime_iff_not_dvd]
  intro hdiv
  haveI : Fintype Q := Fintype.ofFinite Q
  have hcard2 : Fintype.card Q = Nat.card Q := Nat.card_eq_fintype_card.symm
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card k (by rw [hcard2]; exact hdiv)
  have hmem : q ∈ (powMonoidHom k : Q →* Q).ker := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hq])
  rw [hker, Subgroup.mem_bot] at hmem
  exact hk.ne_one (by rw [← hq, hmem, orderOf_one])

/-- **Roots in the `p`-part of a finite cyclic quotient.**  If `k` is prime to `p` and `x` lies in
the `p`-part of `H ⧸ M`, then `x` has a `k`-th root in that `p`-part. -/
theorem Cp_pow_root {p k : ℕ} (hp : p.Prime) (hk : Nat.Coprime k p) (M : OpenNormalSubgroup H)
    [IsCyclic (H ⧸ M.toSubgroup)] {x : H ⧸ M.toSubgroup} (hx : x ∈ Cp p M) :
    ∃ w ∈ Cp p M, w ^ k = x := by
  have hcard : Nat.card ↥(Cp p M) = p ^ vp p M := card_Cp hp M
  have hinj : Function.Injective (fun w : ↥(Cp p M) => w ^ k) := by
    intro a b hab
    have hab' : a ^ k = b ^ k := hab
    have h1 : (a * b⁻¹) ^ k = 1 := by rw [mul_pow, hab', inv_pow, mul_inv_cancel]
    have h2 : orderOf (a * b⁻¹) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf (a * b⁻¹) ∣ p ^ vp p M := hcard ▸ orderOf_dvd_natCard (a * b⁻¹)
    have h4 : orderOf (a * b⁻¹) = 1 :=
      Nat.dvd_one.mp ((hk.pow_right (vp p M)).gcd_eq_one ▸ Nat.dvd_gcd h2 h3)
    exact mul_inv_eq_one.mp (orderOf_eq_one_iff.mp h4)
  obtain ⟨w, hw⟩ := Finite.injective_iff_surjective.mp hinj ⟨x, hx⟩
  refine ⟨(w : H ⧸ M.toSubgroup), w.2, ?_⟩
  simpa using congrArg Subtype.val hw


/-- Closedness of the sets `{y | y ^ k ≡ x (mod M)}` used in the compactness arguments. -/
theorem isClosed_pow_eq_mod (M : OpenNormalSubgroup H) (k : ℕ) (x : H) :
    IsClosed {y : H | QuotientGroup.mk' M.toSubgroup (y ^ k) = QuotientGroup.mk' M.toSubgroup x} := by
  haveI : DiscreteTopology (H ⧸ M.toSubgroup) :=
    QuotientGroup.discreteTopology (N := M.toSubgroup) M.toOpenSubgroup.isOpen'
  exact (isClosed_singleton : IsClosed ({QuotientGroup.mk' M.toSubgroup x} : Set _)).preimage
    ((QuotientGroup.continuous_mk (N := M.toSubgroup)).comp (continuous_id.pow k))

/-- **An element of the `p`-part is an `m`-th power for every `m` prime to `p`.** -/
theorem pPart_le_pCore {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H) :
    pPart p ≤ (pCore p : Subgroup H) := by
  intro x hx
  rw [mem_pCore]
  intro m
  rw [MonoidHom.mem_range]
  set k := (m : ℕ) with hk'
  have hk : Nat.Coprime k p := m.2
  rw [mem_pPart] at hx
  set T : OpenNormalSubgroup H → Set H := fun M =>
    {y : H | QuotientGroup.mk' M.toSubgroup (y ^ k) = QuotientGroup.mk' M.toSubgroup x} with hT
  have hclosed : ∀ M, IsClosed (T M) := fun M => isClosed_pow_eq_mod M k x
  have hne : ∀ M, (T M).Nonempty := by
    intro M
    haveI := quot_isCyclic hcyc M
    obtain ⟨w, -, hw'⟩ := Cp_pow_root hp hk M (hx M)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective M.toSubgroup w
    refine ⟨y, ?_⟩
    show QuotientGroup.mk' M.toSubgroup (y ^ k) = QuotientGroup.mk' M.toSubgroup x
    rw [map_pow, hy, hw']
  have hmono : ∀ M M', M.toSubgroup ≤ M'.toSubgroup → T M ⊆ T M' := by
    intro M M' hle y hy
    show QuotientGroup.mk' M'.toSubgroup (y ^ k) = QuotientGroup.mk' M'.toSubgroup x
    have h1 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
        (QuotientGroup.mk' M.toSubgroup (y ^ k)) = QuotientGroup.mk' M'.toSubgroup (y ^ k) :=
      QuotientGroup.map_mk' _ _ _ _ _
    have h2 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
        (QuotientGroup.mk' M.toSubgroup x) = QuotientGroup.mk' M'.toSubgroup x :=
      QuotientGroup.map_mk' _ _ _ _ _
    rw [← h1, ← h2]
    exact congrArg _ hy
  obtain ⟨y, hy⟩ := nonempty_iInter_of_openNormal T hclosed hne hmono
  refine ⟨y, ?_⟩
  simpa only [powMonoidHom_apply] using eq_of_forall_mk'_eq fun M => Set.mem_iInter.mp hy M

/-- The two descriptions of the `p`-part agree. -/
theorem pCore_eq_pPart {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H) :
    (pCore p : Subgroup H) = pPart p :=
  le_antisymm (pCore_le_pPart hp hcyc) (pPart_le_pCore hp hcyc)

/-- **If every open normal subgroup has index prime to `p`, then `H` is `p`-divisible.** -/
theorem pow_p_surjective_of_not_dvd {p : ℕ} (hp : p.Prime)
    (h : ∀ M : OpenNormalSubgroup H, ¬ p ∣ idx M) : ∀ x : H, ∃ y : H, y ^ p = x := by
  intro x
  set T : OpenNormalSubgroup H → Set H := fun M =>
    {y : H | QuotientGroup.mk' M.toSubgroup (y ^ p) = QuotientGroup.mk' M.toSubgroup x} with hT
  have hclosed : ∀ M, IsClosed (T M) := fun M => isClosed_pow_eq_mod M p x
  have hne : ∀ M, (T M).Nonempty := by
    intro M
    have hcop : Nat.Coprime p (Nat.card (H ⧸ M.toSubgroup)) := by
      rw [quot_card M]
      exact hp.coprime_iff_not_dvd.mpr (h M)
    obtain ⟨w, hw⟩ := pow_surjective_of_coprime_card (k := p) hcop (QuotientGroup.mk' M.toSubgroup x)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective M.toSubgroup w
    refine ⟨y, ?_⟩
    show QuotientGroup.mk' M.toSubgroup (y ^ p) = QuotientGroup.mk' M.toSubgroup x
    rw [map_pow, hy, hw]
  have hmono : ∀ M M', M.toSubgroup ≤ M'.toSubgroup → T M ⊆ T M' := by
    intro M M' hle y hy
    show QuotientGroup.mk' M'.toSubgroup (y ^ p) = QuotientGroup.mk' M'.toSubgroup x
    have h1 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
        (QuotientGroup.mk' M.toSubgroup (y ^ p)) = QuotientGroup.mk' M'.toSubgroup (y ^ p) :=
      QuotientGroup.map_mk' _ _ _ _ _
    have h2 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
        (QuotientGroup.mk' M.toSubgroup x) = QuotientGroup.mk' M'.toSubgroup x :=
      QuotientGroup.map_mk' _ _ _ _ _
    rw [← h1, ← h2]
    exact congrArg _ hy
  obtain ⟨y, hy⟩ := nonempty_iInter_of_openNormal T hclosed hne hmono
  exact ⟨y, eq_of_forall_mk'_eq fun M => Set.mem_iInter.mp hy M⟩

/-- **Some open normal subgroup has `p`-power-divisible index.** -/
theorem exists_openNormal_dvd_of_not_isProPrimeToP {p : ℕ} (hp : p.Prime)
    (hcyc : NK.LocalTame.IsProCyclic H) (h : ¬ NK.LocalTame.IsProPrimeToP p H) :
    ∃ M : OpenNormalSubgroup H, p ∣ idx M := by
  by_contra hc
  push_neg at hc
  have hdiv : ∀ x : H, ∃ y : H, y ^ p = x := pow_p_surjective_of_not_dvd hp hc
  refine h ?_
  intro N hNnorm hNfi
  haveI := hNnorm
  rw [hp.coprime_iff_not_dvd, Subgroup.index_eq_card]
  intro hpdiv
  have hQ : ∀ q : H ⧸ N, ∃ w : H ⧸ N, w ^ p = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨y, hy⟩ := hdiv x
    exact ⟨QuotientGroup.mk' N y, by rw [← map_pow, hy]⟩
  exact (hp.coprime_iff_not_dvd.mp (coprime_card_of_pow_surjective hp hQ)) hpdiv

/-- **The `p`-part of `H` is `ℓ`-divisible for every prime `ℓ ≠ p`.** -/
theorem pCore_pow_divisible {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hcyc : NK.LocalTame.IsProCyclic H) {x : H} (hx : x ∈ (pCore p : Subgroup H)) :
    ∃ y ∈ (pCore p : Subgroup H), y ^ ℓ = x := by
  have hxp : x ∈ pPart p := pCore_le_pPart hp hcyc hx
  rw [mem_pPart] at hxp
  have hℓcop : Nat.Coprime ℓ p := by
    rw [hℓ.coprime_iff_not_dvd]
    intro hd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd)
  set T : OpenNormalSubgroup H → Set H := fun M =>
    {y : H | QuotientGroup.mk' M.toSubgroup (y ^ ℓ) = QuotientGroup.mk' M.toSubgroup x ∧
      QuotientGroup.mk' M.toSubgroup y ∈ Cp p M} with hT
  have hclosed : ∀ M, IsClosed (T M) := by
    intro M
    haveI : DiscreteTopology (H ⧸ M.toSubgroup) :=
      QuotientGroup.discreteTopology (N := M.toSubgroup) M.toOpenSubgroup.isOpen'
    exact (isClosed_pow_eq_mod M ℓ x).inter
      (IsClosed.preimage (QuotientGroup.continuous_mk (N := M.toSubgroup))
        (isClosed_discrete (s := (Cp p M : Set (H ⧸ M.toSubgroup)))))
  have hne : ∀ M, (T M).Nonempty := by
    intro M
    haveI := quot_isCyclic hcyc M
    obtain ⟨w, hw, hw'⟩ := Cp_pow_root hp hℓcop M (hxp M)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective M.toSubgroup w
    refine ⟨y, ?_, ?_⟩
    · show QuotientGroup.mk' M.toSubgroup (y ^ ℓ) = QuotientGroup.mk' M.toSubgroup x
      rw [map_pow, hy, hw']
    · show QuotientGroup.mk' M.toSubgroup y ∈ Cp p M
      rwa [hy]
  have hmono : ∀ M M', M.toSubgroup ≤ M'.toSubgroup → T M ⊆ T M' := by
    intro M M' hle y hy
    haveI := quot_isCyclic hcyc M
    haveI := quot_isCyclic hcyc M'
    have hφ : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
        (QuotientGroup.mk' M.toSubgroup y) = QuotientGroup.mk' M'.toSubgroup y :=
      QuotientGroup.map_mk' _ _ _ _ y
    refine ⟨?_, ?_⟩
    · show QuotientGroup.mk' M'.toSubgroup (y ^ ℓ) = QuotientGroup.mk' M'.toSubgroup x
      have h1 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
          (QuotientGroup.mk' M.toSubgroup (y ^ ℓ)) = QuotientGroup.mk' M'.toSubgroup (y ^ ℓ) :=
        QuotientGroup.map_mk' _ _ _ _ _
      have h2 : QuotientGroup.map M.toSubgroup M'.toSubgroup (MonoidHom.id H) hle
          (QuotientGroup.mk' M.toSubgroup x) = QuotientGroup.mk' M'.toSubgroup x :=
        QuotientGroup.map_mk' _ _ _ _ _
      rw [← h1, ← h2]
      exact congrArg _ hy.1
    · show QuotientGroup.mk' M'.toSubgroup y ∈ Cp p M'
      rw [← hφ, ← map_Cp_eq hp hle]
      exact ⟨QuotientGroup.mk' M.toSubgroup y, hy.2, rfl⟩
  obtain ⟨y, hy⟩ := nonempty_iInter_of_openNormal T hclosed hne hmono
  have hy1 : ∀ M : OpenNormalSubgroup H,
      QuotientGroup.mk' M.toSubgroup (y ^ ℓ) = QuotientGroup.mk' M.toSubgroup x :=
    fun M => (Set.mem_iInter.mp hy M).1
  have hy2 : ∀ M : OpenNormalSubgroup H, QuotientGroup.mk' M.toSubgroup y ∈ Cp p M :=
    fun M => (Set.mem_iInter.mp hy M).2
  exact ⟨y, pPart_le_pCore hp hcyc (mem_pPart.mpr hy2), eq_of_forall_mk'_eq hy1⟩

/-- **The `p`-part of `H` is nontrivial as soon as `H` is not pro-prime-to-`p`.** -/
theorem pCore_ne_bot {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H)
    (h : ¬ NK.LocalTame.IsProPrimeToP p H) : (pCore p : Subgroup H) ≠ ⊥ := by
  obtain ⟨M₁, hM₁⟩ := exists_openNormal_dvd_of_not_isProPrimeToP hp hcyc h
  haveI := quot_isCyclic hcyc M₁
  haveI : Fact p.Prime := ⟨hp⟩
  have hv : 1 ≤ vp p M₁ := one_le_padicValNat_of_dvd (idx_ne_zero M₁) hM₁
  have hcard : 1 < Nat.card ↥(Cp p M₁) := by
    rw [card_Cp hp M₁]
    calc 1 < 2 := one_lt_two
      _ ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ vp p M₁ := Nat.pow_le_pow_right hp.pos hv
  haveI : Nontrivial ↥(Cp p M₁) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Cp p M₁))
  have hcne : ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup) ≠ 1 :=
    fun hcon => hc (Subtype.ext hcon)
  set T : OpenNormalSubgroup H → Set H := fun M =>
    {y : H | QuotientGroup.mk' M₁.toSubgroup y = ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup) ∧
      QuotientGroup.mk' M.toSubgroup y ∈ Cp p M} with hT
  have hclosed : ∀ M, IsClosed (T M) := by
    intro M
    haveI : DiscreteTopology (H ⧸ M₁.toSubgroup) :=
      QuotientGroup.discreteTopology (N := M₁.toSubgroup) M₁.toOpenSubgroup.isOpen'
    haveI : DiscreteTopology (H ⧸ M.toSubgroup) :=
      QuotientGroup.discreteTopology (N := M.toSubgroup) M.toOpenSubgroup.isOpen'
    exact (IsClosed.preimage (QuotientGroup.continuous_mk (N := M₁.toSubgroup))
        (isClosed_singleton (x := ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup)))).inter
      (IsClosed.preimage (QuotientGroup.continuous_mk (N := M.toSubgroup))
        (isClosed_discrete (s := (Cp p M : Set (H ⧸ M.toSubgroup)))))
  have hne : ∀ M, (T M).Nonempty := by
    intro M
    haveI := quot_isCyclic hcyc M₁
    haveI := quot_isCyclic hcyc M
    haveI := quot_isCyclic hcyc (M₁ ⊓ M)
    have hle₁ : ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H) ≤ (M₁ : Subgroup H) := inf_le_left
    have hle₂ : ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H) ≤ (M : Subgroup H) := inf_le_right
    have hcM : ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup) ∈ (Cp p (M₁ ⊓ M)).map
        (QuotientGroup.map ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H) (M₁ : Subgroup H)
          (MonoidHom.id H) hle₁) := by
      rw [map_Cp_eq hp hle₁]
      exact c.2
    obtain ⟨c', hc'1, hc'2⟩ := hcM
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H) c'
    have hy' : ((y : H) : H ⧸ ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)) = c' := hy
    refine ⟨y, ?_, ?_⟩
    · show ((y : H) : H ⧸ (M₁ : Subgroup H)) = ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup)
      have h1 : QuotientGroup.map ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)
          (M₁ : Subgroup H) (MonoidHom.id H) hle₁
          ((y : H) : H ⧸ ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)) =
          (y : H ⧸ (M₁ : Subgroup H)) :=
        QuotientGroup.map_mk _ _ _ _ _
      have hc'2' : QuotientGroup.map ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)
          (M₁ : Subgroup H) (MonoidHom.id H) hle₁
          ((y : H) : H ⧸ ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)) =
          ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup) := by
        rw [hy']
        exact hc'2
      exact h1.symm.trans hc'2'
    · show ((y : H) : H ⧸ (M : Subgroup H)) ∈ Cp p M
      have h2 : QuotientGroup.map ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)
          (M : Subgroup H) (MonoidHom.id H) hle₂
          ((y : H) : H ⧸ ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)) ∈ Cp p M := by
        rw [← map_Cp_eq hp hle₂]
        exact ⟨c', hc'1, by rw [hy']⟩
      have h3 : QuotientGroup.map ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)
          (M : Subgroup H) (MonoidHom.id H) hle₂
          ((y : H) : H ⧸ ((M₁ ⊓ M : OpenNormalSubgroup H) : Subgroup H)) =
          (y : H ⧸ (M : Subgroup H)) :=
        QuotientGroup.map_mk _ _ _ _ _
      rwa [h3] at h2
  have hmono : ∀ M M', M.toSubgroup ≤ M'.toSubgroup → T M ⊆ T M' := by
    intro M M' hle y hy
    haveI := quot_isCyclic hcyc M
    haveI := quot_isCyclic hcyc M'
    refine ⟨hy.1, ?_⟩
    have h1 : QuotientGroup.map (M : Subgroup H) (M' : Subgroup H) (MonoidHom.id H) hle
        ((y : H) : H ⧸ (M : Subgroup H)) ∈ Cp p M' := by
      rw [← map_Cp_eq hp hle]
      exact ⟨QuotientGroup.mk' M.toSubgroup y, hy.2, rfl⟩
    have h4 : QuotientGroup.map (M : Subgroup H) (M' : Subgroup H) (MonoidHom.id H) hle
        ((y : H) : H ⧸ (M : Subgroup H)) = (y : H ⧸ (M' : Subgroup H)) :=
      QuotientGroup.map_mk _ _ _ _ _
    rw [h4] at h1
    exact h1
  obtain ⟨y, hy⟩ := nonempty_iInter_of_openNormal T hclosed hne hmono
  have hy1 : QuotientGroup.mk' M₁.toSubgroup y = ((c : ↥(Cp p M₁)) : H ⧸ M₁.toSubgroup) :=
    (Set.mem_iInter.mp hy M₁).1
  have hy2 : ∀ M : OpenNormalSubgroup H, QuotientGroup.mk' M.toSubgroup y ∈ Cp p M :=
    fun M => (Set.mem_iInter.mp hy M).2
  have hynot : y ≠ 1 := by
    intro h1
    rw [h1, map_one] at hy1
    exact hcne hy1.symm
  intro hbot
  rw [Subgroup.eq_bot_iff_forall] at hbot
  exact hynot (hbot y (pPart_le_pCore hp hcyc (mem_pPart.mpr hy2)))


/-- An integer all of whose prime divisors are `p` is a power of `p`. -/
theorem eq_prime_pow_of_forall_prime_dvd {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ = p) : n = p ^ padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ padicValNat p n ∣ n :=
    (padicValNat_dvd_iff_le (a := n) (n := padicValNat p n) hn).mpr le_rfl
  have hm : n / p ^ padicValNat p n = 1 := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd hne
    have hℓn : ℓ ∣ n := dvd_trans hℓdvd (Nat.div_dvd_of_dvd hdvd)
    have hℓp : ℓ = p := h ℓ hℓ hℓn
    subst hℓp
    exact (hp.coprime_iff_not_dvd.mp (coprime_div_valuation hp hn).symm) hℓdvd
  have hcancel := Nat.div_mul_cancel hdvd
  rw [hm, one_mul] at hcancel
  exact hcancel.symm

/-- **The `p`-part of `H` is characteristic.** -/
theorem pCore_characteristic (p : ℕ) : (pCore p : Subgroup H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    have hx' := mem_pCore.mp hx
    refine mem_pCore.mpr fun m => ?_
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hx' m)
    simp only [powMonoidHom_apply] at hz
    refine MonoidHom.mem_range.mpr ⟨φ z, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hz]
    rfl
  · intro y hy
    have hy' := mem_pCore.mp hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    refine mem_pCore.mpr fun m => ?_
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hy' m)
    simp only [powMonoidHom_apply] at hw
    refine MonoidHom.mem_range.mpr ⟨φ.symm w, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hw]

/-- **The `p`-part of `H` is pro-`p`.** -/
theorem isProP_pCore {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H) :
    NK.LocalTame.IsProP p ↥(pCore p : Subgroup H) := by
  intro R hRnorm hRfi
  haveI := hRnorm
  haveI := hRfi
  haveI : Finite (↥(pCore p : Subgroup H) ⧸ R) := inferInstance
  have hne : R.index ≠ 0 := hRfi.index_ne_zero
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ R.index → ℓ = p := by
    intro ℓ hℓ hℓdvd
    by_contra hℓp
    have hdiv : ∀ q : (↥(pCore p : Subgroup H) ⧸ R), ∃ w, w ^ ℓ = q := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
      obtain ⟨y, hy, hy'⟩ := pCore_pow_divisible hp hℓ hℓp hcyc x.2
      refine ⟨QuotientGroup.mk' R ⟨y, hy⟩, ?_⟩
      rw [← map_pow]
      exact congrArg (QuotientGroup.mk' R) (Subtype.ext hy')
    have hcop : Nat.Coprime ℓ (Nat.card (↥(pCore p : Subgroup H) ⧸ R)) :=
      coprime_card_of_pow_surjective hℓ hdiv
    rw [← Subgroup.index_eq_card R] at hcop
    exact (hℓ.coprime_iff_not_dvd.mp hcop) hℓdvd
  exact ⟨_, eq_prime_pow_of_forall_prime_dvd hp hne hprime⟩

/-- The `p`-part of a pro-cyclic profinite group `H` is a characteristic pro-`p` subgroup, and it
is nontrivial as soon as `H` is not pro-prime-to-`p`. -/
theorem exists_characteristic_proP_of_not_isProPrimeToP {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [CompactSpace H]
    [TotallyDisconnectedSpace H] {p : ℕ} (hp : p.Prime) (hcyc : NK.LocalTame.IsProCyclic H)
    (h : ¬ NK.LocalTame.IsProPrimeToP p H) :
    ∃ N : Subgroup H, N.Characteristic ∧ N ≠ ⊥ ∧ NK.LocalTame.IsProP p ↥N := by
  have hcomm : ∀ x y : H, x * y = y * x :=
    NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite hcyc
  letI : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  exact ⟨(pCore p : Subgroup H), pCore_characteristic p, pCore_ne_bot hp hcyc h,
    isProP_pCore hp hcyc⟩

end

end NK.TameStructure.ProCyclic
