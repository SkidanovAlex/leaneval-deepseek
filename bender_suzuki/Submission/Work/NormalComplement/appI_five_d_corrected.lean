import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_five_c_prime
import Submission.Work.NormalComplement.appI_four

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Helper lemmas for Appendix I (5)(d)

Frattini/Sylow bookkeeping, independent of the group-theoretic content of (5)(d): the decomposition
of an element of `Y` as `m · n` with `m ∈ M ⊴ Y` and `n ∈ N_Y(P)` for `P` a Sylow `p`-subgroup of
`M`, the transport of Sylow-ness to intermediate subgroups, and the description of a product of
subgroups as a join. -/

/-- `|H.subgroupOf Y| = |H|` for `H ≤ Y`. -/
lemma card_subgroupOf_eq_of_le {H Y : Subgroup G} (h : H ≤ Y) :
    Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- Conjugating a `p`-Sylow gives a `p`-Sylow of the conjugate subgroup. -/
lemma isSylowIn_map_conj {p : ℕ} {A X : Subgroup G} (hA : IsSylowIn p A X) (g : G) :
    IsSylowIn p (A.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map _, Subgroup.map_mono hA.2.1, ?_⟩
  have h : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf
      (X.map (MulAut.conj g).toMonoidHom)).index = (A.subgroupOf X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A X
      (MulAut.conj g).injective
  rw [h]
  exact hA.2.2

/-- Two `p`-Sylow subgroups of a subgroup `X` are conjugate by an element of `X`. -/
lemma exists_conj_map_eq_of_isSylowIn {p : ℕ} (hp : p.Prime) {A B X : Subgroup G}
    (hA : IsSylowIn p A X) (hB : IsSylowIn p B X) :
    ∃ g ∈ X, A.map (MulAut.conj g).toMonoidHom = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA' : IsPGroup p (A.subgroupOf X) :=
    hA.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  have hB' : IsPGroup p (B.subgroupOf X) :=
    hB.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X) (hA'.toSylow hA.2.2) (hB'.toSylow hB.2.2)
  have hcoe : (↑(g • hA'.toSylow hA.2.2) : Subgroup ↥X) = ↑(hB'.toSylow hB.2.2) := congrArg _ hg
  have h1 : (↑(g • hA'.toSylow hA.2.2) : Subgroup ↥X)
      = (A.subgroupOf X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have h2 : (↑(hB'.toSylow hB.2.2) : Subgroup ↥X) = B.subgroupOf X :=
    IsPGroup.toSylow_coe hB' hB.2.2
  have hsmul : (A.subgroupOf X).map (MulAut.conj g).toMonoidHom = B.subgroupOf X := by
    rw [← h1, hcoe, h2]
  refine ⟨(g : G), g.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    have h3 : (⟨a, hA.2.1 ha⟩ : ↥X) ∈ A.subgroupOf X := by
      simpa [Subgroup.mem_subgroupOf] using ha
    have h4 : (MulAut.conj g) (⟨a, hA.2.1 ha⟩ : ↥X) ∈ B.subgroupOf X := by
      rw [← hsmul]
      exact ⟨_, h3, rfl⟩
    rw [Subgroup.mem_subgroupOf] at h4
    rw [← hax]
    simpa [MulAut.conj_apply] using h4
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
    have hcard : Nat.card ↥(A.subgroupOf X) = Nat.card ↥(B.subgroupOf X) := by
      rw [← hsmul]
      exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    rw [← card_subgroupOf_eq_of_le hA.2.1, ← card_subgroupOf_eq_of_le hB.2.1, hcard]

/-- A `p`-Sylow of `E` is a `p`-Sylow of every intermediate subgroup `P ≤ N ≤ E`. -/
lemma sylowIn_of_le_of_le {p : ℕ} {P N E : Subgroup G} (hP : IsSylowIn p P E) (hPN : P ≤ N)
    (hNE : N ≤ E) : IsSylowIn p P N := by
  refine ⟨hP.1, hPN, ?_⟩
  intro hdiv
  have hrel : P.relIndex N ∣ P.relIndex E :=
    ⟨N.relIndex E, (Subgroup.relIndex_mul_relIndex P N E hPN hNE).symm⟩
  exact hP.2.2 (hdiv.trans hrel)

/-- **Frattini's argument**, membership form: for `M ⊴ Y` and `P` a `p`-Sylow of `M`, every
`y ∈ Y` is a product `m * n` with `m ∈ M` and `n ∈ N_Y(P)`. -/
lemma frattini_decomp {p : ℕ} (hp : p.Prime) {M Y : Subgroup G} (hMY : M ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) {P : Subgroup G}
    (hP : IsSylowIn p P M) :
    ∀ y ∈ Y, ∃ m ∈ M, ∃ n ∈ Subgroup.normalizer (P : Set G) ⊓ Y, y = m * n := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hy
  have hPy : IsSylowIn p (P.map (MulAut.conj y).toMonoidHom) M := by
    have h1 : M.map (MulAut.conj y).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer_iff.mpr hnorm hy)
    have h2 := isSylowIn_map_conj hP y
    rwa [h1] at h2
  obtain ⟨m, hm, hmeq⟩ := exists_conj_map_eq_of_isSylowIn hp hPy hP
  -- `m (y P y⁻¹) m⁻¹ = P`, so `m * y ∈ N_G(P)` and `y = m⁻¹ * (m * y)`
  have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj y).toMonoidHom
      = (MulAut.conj (m * y)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hkey : P.map (MulAut.conj (m * y)).toMonoidHom = P := by
    rw [← hcomp, ← Subgroup.map_map]
    exact hmeq
  have hn : m * y ∈ Subgroup.normalizer (P : Set G) ⊓ Y := by
    refine Subgroup.mem_inf.mpr ⟨?_, Y.mul_mem (hMY hm) hy⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hkey
  refine ⟨m⁻¹, M.inv_mem hm, m * y, hn, ?_⟩
  group

/-- A product of two subgroups, the right factor normalising the left, is the join. -/
lemma mem_sup_mul {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B h, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- Membership in the image of a subgroup under conjugation by `t`. -/
lemma mem_map_conj_iff {A : Subgroup G} {t x : G} :
    x ∈ A.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * x * t ∈ A := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    have h : (MulAut.conj t).toMonoidHom a = t * a * t⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h] at hax
    have h2 : t⁻¹ * x * t = a := by
      rw [← hax]
      group
    rwa [h2]
  · intro hx
    refine ⟨t⁻¹ * x * t, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- A factor commuting with `t` can be taken out of a `t`-commutator: the element
`[t, z·n] = t⁻¹(z n)⁻¹t(z n)` equals the conjugate `n⁻¹[t,z]n` of `[t,z]`. -/
lemma kapp_conj_mul_of_comm {t n z : G} (h : n * t = t * n) :
    t⁻¹ * (z * n)⁻¹ * t * (z * n) = n⁻¹ * (t⁻¹ * z⁻¹ * t * z) * n := by
  have h1 : t⁻¹ * n⁻¹ = n⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, h]
  rw [mul_inv_rev,
    show t⁻¹ * (n⁻¹ * z⁻¹) * t * (z * n) = (t⁻¹ * n⁻¹) * z⁻¹ * (t * z) * n from by group,
    h1]
  group

/-- **Peterfalvi I Appendix I (5)(d)** (p.201) in the case `d = 2` used by Chapter III, with the
hypothesis `C_K(P) = 1` stated with the correct binder order.

(`Submission.Work.NormalComplement.appI_five_d` has `∀ k ∈ K, ∀ q ∈ P, q*k*q⁻¹ = k → k = 1`, which
with `1 ∈ P` forces `K = {1}` and is therefore useless; the source's `C_K(P) = 1` is
`∀ k ∈ K, (∀ q ∈ P, q*k*q⁻¹ = k) → k = 1`, as used here.  The `d = 2` restriction matches the only
case Chapter III needs and the available proof of (5)(c) — see the reviewer's caution about
`d` odd with `X` even.)

`t` is an involution normalising the odd-order solvable `X`, `E ⊴ X`, `P` a `p`-Sylow of `E` with
`P ≤ V = C_X(t)` and `C_K(P) = 1` (`K = Kapp t X = {[t,x] : x ∈ X}`); then `K ⊆ [E,E]` and
`t E t⁻¹ ≤ E`.

Route.  App. I (5)(c) (the first half of `Work.NormalComplement.appI_five_c_prime`, with `U = P`)
gives `N_X(P) ⊆ V = C_X(t)`.  Let `N = E ∩ tEt⁻¹`; it is normalised by `E` and `P ≤ N` is a Sylow
`p`-subgroup of `N`, so Frattini gives `E = N · N_E(P)`, and since `N_E(P) ⊆ N_X(P) ⊆ V` is
pointwise fixed by `t` while `N` is `t`-invariant, we get `tEt⁻¹ = t(N · N_E(P))t⁻¹ = N · N_E(P)
= E`.  (This replaces the source's "so `t` centralises `X/E`", which already needs `t` to normalise
`E`; the argument above needs only the `t`-invariance of `N`.)  Frattini in `X` for `P ≤ E ⊴ X`
gives `X = E · N_X(P) ⊆ E · V`, so `K = Kapp t X ⊆ E`.  Finally `R = ⁅E,E⁆ ⊔ P ⊴ E` with `P` a
Sylow `p`-subgroup of `R`, so Frattini gives `E = R · N_E(P)`; the images of `R = ⁅E,E⁆ · P` and of
`N_E(P) ⊆ C(t)` in the abelian quotient `E/⁅E,E⁆` generate it and are fixed by `t`, so `t` acts
trivially on `E/⁅E,E⁆`; every `z ∈ K` is `[t,e]` with `e ∈ E`, hence `z ∈ ⁅E,E⁆`. -/
theorem appI_five_d_corrected {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hodd : Odd (Nat.card X)) (hsolv : Group.IsSolvable X) {E : Subgroup G}
    (hE : E ≤ X) (hEX : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) {p : ℕ} {P : Subgroup G}
    (hPsyl : Work.NormalComplement.IsSylowIn p P E)
    (hPV : P ≤ Subgroup.centralizer ({t} : Set G) ⊓ X) (hp : p.Prime)
    (hCK : ∀ k ∈ Work.NormalComplement.Kapp t X, (∀ q ∈ P, q * k * q⁻¹ = k) → k = 1) :
    Work.NormalComplement.Kapp t X ⊆ ((⁅E, E⁆ : Subgroup G) : Set G) ∧
      ∀ e ∈ E, t * e * t⁻¹ ∈ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- ## Elementary consequences of `t` being an involution
  have ht2 : t * t = 1 := by
    have h : t ^ orderOf t = 1 := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htXinv : ∀ x ∈ X, t⁻¹ * x * t ∈ X := by
    intro x hx
    simpa only [htinv] using htX x hx
  have hcomm_of_mem_centralizer : ∀ {z : G}, z ∈ Subgroup.centralizer ({t} : Set G) →
      t * z * t⁻¹ = z := fun hz =>
    conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hz).symm
  have hcomm_inv_of_mem_centralizer : ∀ {z : G}, z ∈ Subgroup.centralizer ({t} : Set G) →
      t⁻¹ * z * t = z := fun hz => by
    simpa only [htinv] using hcomm_of_mem_centralizer hz
  -- ## App. I (5)(c): the elements of `X` normalising `P` lie in `V = C_X(t)`
  have hNXP : ∀ z ∈ X, (∀ u ∈ P, z * u * z⁻¹ ∈ P) →
      z ∈ Subgroup.centralizer ({t} : Set G) ⊓ X :=
    ((appI_five_c_prime (d := 2) Nat.prime_two ht htX (Nat.coprime_two_right.mpr hodd) hsolv hp
      hPV hPsyl.1).1 hCK)
  have hNX_le_V : (X ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.centralizer ({t} : Set G) ⊓ X := fun z hz =>
    hNXP z hz.1 (fun u hu => (Subgroup.mem_normalizer_iff.mp hz.2 u).mp hu)
  have hNE_le_V : (E ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.centralizer ({t} : Set G) ⊓ X := fun z hz => hNX_le_V ⟨hE hz.1, hz.2⟩
  have hNE_eq_self : ∀ z ∈ E ⊓ Subgroup.normalizer (P : Set G), t * z * t⁻¹ = z :=
    fun z hz => hcomm_of_mem_centralizer (hNE_le_V hz).1
  have hNE_fix : ∀ z ∈ E ⊓ Subgroup.normalizer (P : Set G), t⁻¹ * z * t = z :=
    fun z hz => hcomm_inv_of_mem_centralizer (hNE_le_V hz).1
  -- ## Step 1: `t` normalises `E`
  set Et : Subgroup G := E.map (MulAut.conj t).toMonoidHom with hEtdef
  have hN_norm : ∀ y ∈ E, ∀ m ∈ E ⊓ Et, y * m * y⁻¹ ∈ E ⊓ Et := by
    intro y hy m hm
    obtain ⟨hmE, hmEt⟩ := Subgroup.mem_inf.mp hm
    rw [hEtdef, mem_map_conj_iff] at hmEt
    refine Subgroup.mem_inf.mpr ⟨hEX y (hE hy) m hmE, ?_⟩
    rw [hEtdef, mem_map_conj_iff]
    have hmem : t⁻¹ * (y * m * y⁻¹) * t
        = (t⁻¹ * y * t) * (t⁻¹ * m * t) * (t⁻¹ * y * t)⁻¹ := by group
    rw [hmem]
    exact hEX (t⁻¹ * y * t) (htXinv y (hE hy)) (t⁻¹ * m * t) hmEt
  have hP_inf : P ≤ E ⊓ Et := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨hPsyl.2.1 hq, ?_⟩
    rw [hEtdef, mem_map_conj_iff, hcomm_inv_of_mem_centralizer (hPV hq).1]
    exact hPsyl.2.1 hq
  have hP_M : IsSylowIn p P (E ⊓ Et) := sylowIn_of_le_of_le hPsyl hP_inf inf_le_left
  have hE_subset_Et : E ≤ Et := by
    intro y hy
    obtain ⟨m, hm, n, hn, rfl⟩ := frattini_decomp hp inf_le_left hN_norm hP_M y hy
    have hnEt : n ∈ Et := by
      rw [hEtdef, mem_map_conj_iff, hNE_fix n (Subgroup.mem_inf.mpr ⟨hn.2, hn.1⟩)]
      exact hn.2
    exact Et.mul_mem hm.2 hnEt
  have hEt_eq_E : Et = E := by
    have hcard : Nat.card ↥Et = Nat.card ↥E := by
      rw [hEtdef, Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact (Subgroup.eq_of_le_of_card_ge hE_subset_Et (le_of_eq hcard)).symm
  have hEt_map : E.map (MulAut.conj t).toMonoidHom = E := hEtdef.symm.trans hEt_eq_E
  have htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E := by
    intro e he
    have h1 : e ∈ Et := hE_subset_Et he
    rw [hEtdef, mem_map_conj_iff] at h1
    simpa only [htinv] using h1
  -- ## Step 2: `X = E · V`
  have hX_decomp : ∀ x ∈ X, ∃ e ∈ E, ∃ v ∈ Subgroup.centralizer ({t} : Set G) ⊓ X,
      x = e * v := by
    intro x hx
    obtain ⟨m, hm, n, hn, rfl⟩ := frattini_decomp hp hE hEX hPsyl x hx
    exact ⟨m, hm, n, hNX_le_V ⟨hn.2, hn.1⟩, rfl⟩
  -- ## Step 3: `t` acts trivially on `E / ⁅E,E⁆`
  have hEE_le_E : (⁅E, E⁆ : Subgroup G) ≤ E := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
  have hEE_conj : ∀ y ∈ E, (⁅E, E⁆ : Subgroup G).map (MulAut.conj y).toMonoidHom = ⁅E, E⁆ := by
    intro y hy
    have hEy : E.map (MulAut.conj y).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)
    rw [Subgroup.map_commutator, hEy]
  have hEE_conj_mem : ∀ y ∈ E, ∀ c ∈ (⁅E, E⁆ : Subgroup G), y * c * y⁻¹ ∈ ⁅E, E⁆ := by
    intro y hy c hc
    rw [← hEE_conj y hy]
    exact Subgroup.mem_map.mpr ⟨c, hc, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hEE_t : (⁅E, E⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅E, E⁆ := by
    rw [Subgroup.map_commutator, hEt_map]
  have hEE_t_mem : ∀ c ∈ (⁅E, E⁆ : Subgroup G), t * c * t⁻¹ ∈ ⁅E, E⁆ := by
    intro c hc
    rw [← hEE_t]
    exact Subgroup.mem_map.mpr ⟨c, hc, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hEE_tinv_mem : ∀ c ∈ (⁅E, E⁆ : Subgroup G), t⁻¹ * c * t ∈ ⁅E, E⁆ := fun c hc => by
    simpa only [htinv] using hEE_t_mem c hc
  have hP_normalizes_EE : P ≤ Subgroup.normalizer ((⁅E, E⁆ : Subgroup G) : Set G) :=
    fun q hq => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hEE_conj q (hPsyl.2.1 hq))
  set R : Subgroup G := ⁅E, E⁆ ⊔ P with hRdef
  have hR_le_E : R ≤ E := sup_le hEE_le_E hPsyl.2.1
  have hR_norm : ∀ y ∈ E, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨c, hc, q, hq, rfl⟩ := (mem_sup_mul hP_normalizes_EE).mp hr
    have h1 : y * c * y⁻¹ ∈ ⁅E, E⁆ := hEE_conj_mem y hy c hc
    have h2 : y * q * y⁻¹ ∈ R := by
      have hcq : ⁅y, q⁆ ∈ ⁅E, E⁆ := Subgroup.commutator_mem_commutator hy (hPsyl.2.1 hq)
      have hsum : ⁅y, q⁆ * q ∈ R :=
        (mem_sup_mul hP_normalizes_EE).mpr ⟨_, hcq, q, hq, rfl⟩
      have hsq : y * q * y⁻¹ = ⁅y, q⁆ * q := by
        rw [← conj_eq_commutatorElement_mul, MulAut.conj_apply]
      rw [hsq]
      exact hsum
    rw [show y * (c * q) * y⁻¹ = (y * c * y⁻¹) * (y * q * y⁻¹) from by group]
    exact R.mul_mem (Subgroup.mem_sup_left h1) h2
  have hP_R : IsSylowIn p P R := sylowIn_of_le_of_le hPsyl le_sup_right hR_le_E
  have hcomm_E : ∀ u ∈ E, t⁻¹ * u⁻¹ * t * u ∈ ⁅E, E⁆ := by
    intro u hu
    obtain ⟨r, hr, n, hn, rfl⟩ := frattini_decomp hp hR_le_E hR_norm hP_R u hu
    have hnC : n ∈ Subgroup.centralizer ({t} : Set G) :=
      (hNE_le_V (Subgroup.mem_inf.mpr ⟨hn.2, hn.1⟩)).1
    have hnt : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp hnC
    have hmain : n⁻¹ * (t⁻¹ * r⁻¹ * t * r) * n ∈ ⁅E, E⁆ := by
      have hX : t⁻¹ * r⁻¹ * t * r ∈ ⁅E, E⁆ := by
        obtain ⟨c, hc, q, hq, rfl⟩ := (mem_sup_mul hP_normalizes_EE).mp hr
        have hqt : q * t = t * q := Subgroup.mem_centralizer_singleton_iff.mp (hPV hq).1
        have hin : t⁻¹ * c⁻¹ * t * c ∈ ⁅E, E⁆ :=
          (⁅E, E⁆ : Subgroup G).mul_mem
            (hEE_tinv_mem c⁻¹ ((⁅E, E⁆ : Subgroup G).inv_mem hc)) hc
        rw [kapp_conj_mul_of_comm hqt]
        simpa using hEE_conj_mem q⁻¹ (E.inv_mem (hPsyl.2.1 hq)) (t⁻¹ * c⁻¹ * t * c) hin
      simpa using hEE_conj_mem n⁻¹ (E.inv_mem hn.2) (t⁻¹ * r⁻¹ * t * r) hX
    rw [kapp_conj_mul_of_comm hnt]
    exact hmain
  -- ## Conclusion
  constructor
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨m, hm, n, hn, hxmn⟩ := hX_decomp x hx
    have hm' : n⁻¹ * m * n ∈ E := by
      simpa using hEX n⁻¹ (X.inv_mem hn.2) m hm
    have hcomm_n : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp hn.1
    have hx' : x = n * (n⁻¹ * m * n) := by rw [hxmn]; group
    rw [hx', kappArg_mul_left (t := t) (d := n) (z := n⁻¹ * m * n) hcomm_n]
    exact hcomm_E (n⁻¹ * m * n) hm'
  · exact htE

end Work.NormalComplement
