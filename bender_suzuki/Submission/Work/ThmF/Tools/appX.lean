import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.Fitting.Main
import Submission.Work.Coprime.abelian_split
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup
import Submission.Work.PGroup.normal_typePP_of_not_isCyclic
import Submission.Work.PGroup.Basic
import Submission.Work.LocalPrelim.Defs
import Submission.Work.ThmF.Tools.appX_card_E
import Submission.Work.ThmF.Tools.appX_cyclic_fitting
import Submission.Work.ThmF.Tools.appX_fpf_fitting
import Submission.Work.ThmF.Tools.appX_commutator_le_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Tools

/-! ## Auxiliary lemmas for `appX` (Peterfalvi II, Appendix X)

`appX` is the Proposition of Appendix X of Peterfalvi II (p. 281):
*let `D` be a group of odd order acting faithfully on an elementary abelian `q`-group `E` and
transitively on `E^#`. Then `F(D)` is cyclic and acts fixed-point-freely on `E`, and `D/F(D)` is
abelian.*  The proof needs Huppert's special case (the Lemma of p. 281) together with
Feit–Thompson (`D` is solvable) and Fitting's theorem (`C_D(F(D)) ≤ F(D)`).

The first auxiliary lemma is the combinatorial heart of the Appendix X Lemma: if a group acts on
an internal direct product `E = E₁ · E₂` preserving both factors, fails to fix any nonidentity
element for some nonidentity group element, and the stabilisers of all nonidentity elements have
the same cardinality, then in fact every nonidentity element acts fixed-point-freely. -/

section DirectProduct

variable {E : Type*} [Group E]

/-- The stabiliser of a point `a` of `E` under the action of `P`, as a subgroup of `P`. -/
private def stab (P : Type*) [Group P] [MulDistribMulAction P E] (a : E) : Subgroup P where
  carrier := {p : P | p • a = a}
  mul_mem' := by intro x y hx hy; show (x * y) • a = a; rw [mul_smul, hy, hx]
  one_mem' := by show (1 : P) • a = a; rw [one_smul]
  inv_mem' := by intro x hx; show x⁻¹ • a = a; rw [← hx, inv_smul_smul, hx]

/-- The fixed points of a single element `p` of the acting group, as a subgroup. -/
private def fixSub (P : Type*) [Group P] [MulDistribMulAction P E] (p : P) : Subgroup E where
  carrier := {a : E | p • a = a}
  mul_mem' := by intro x y hx hy; show p • (x * y) = x * y; rw [smul_mul', hx, hy]
  one_mem' := by show p • (1 : E) = 1; rw [smul_one]
  inv_mem' := by intro x hx; show p • x⁻¹ = x⁻¹; rw [smul_inv', hx]

/-- Uniqueness of the decomposition in an internal direct product. -/
private lemma eq_of_mul_eq_mul_of_inf_eq_bot {E₁ E₂ : Subgroup E} (hinf : E₁ ⊓ E₂ = ⊥)
    {x x' y y' : E} (hx : x ∈ E₁) (hx' : x' ∈ E₁) (hy : y ∈ E₂) (hy' : y' ∈ E₂)
    (h : x * y = x' * y') : x = x' ∧ y = y' := by
  have h1 : x⁻¹ * x' = y * y'⁻¹ := by
    calc x⁻¹ * x' = x⁻¹ * (x' * y') * y'⁻¹ := by group
      _ = x⁻¹ * (x * y) * y'⁻¹ := by rw [← h]
      _ = y * y'⁻¹ := by group
  have hmem : x⁻¹ * x' ∈ E₁ ⊓ E₂ :=
    ⟨E₁.mul_mem (E₁.inv_mem hx) hx', by rw [h1]; exact E₂.mul_mem hy (E₂.inv_mem hy')⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have hxx : x = x' := inv_mul_eq_one.mp hmem
  refine ⟨hxx, ?_⟩
  have h2 : x * y = x * y' := by rw [← hxx] at h; exact h
  exact mul_left_cancel h2

/-- **Direct-product form of the Appendix X Lemma.**  Let a finite group `P` act on a group `E`
preserving a direct decomposition `E = E₁ · E₂` into two nontrivial factors, and assume that the
stabilisers of all nonidentity points of `E` have the same cardinality.  Then `P` acts
fixed-point-freely on `E^#`. -/
private theorem fpf_of_directProduct {P : Type*} [Group P] [Finite P]
    [MulDistribMulAction P E] (E₁ E₂ : Subgroup E) (hinf : E₁ ⊓ E₂ = ⊥) (hsup : E₁ ⊔ E₂ = ⊤)
    (hnt₁ : E₁ ≠ ⊥) (hnt₂ : E₂ ≠ ⊥)
    (hinv₁ : ∀ p : P, ∀ x : E, x ∈ E₁ ↔ p • x ∈ E₁)
    (hinv₂ : ∀ p : P, ∀ x : E, x ∈ E₂ ↔ p • x ∈ E₂)
    (hfaith : ∀ p : P, (∀ a : E, p • a = a) → p = 1)
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 → Nat.card (stab P a) = Nat.card (stab P b)) :
    ∀ p : P, p ≠ 1 → ∀ a : E, p • a = a → a = 1 := by
  -- The stabilisers of `a ∈ E₁^#` and `b ∈ E₂^#` coincide.
  have key : ∀ a ∈ E₁, a ≠ 1 → ∀ b ∈ E₂, b ≠ 1 → stab P a = stab P b := by
    intro a ha ha1 b hb hb1
    have hab : a * b ≠ 1 := by
      intro h
      have hmem : a ∈ E₁ ⊓ E₂ :=
        ⟨ha, by rw [mul_eq_one_iff_eq_inv.mp h]; exact E₂.inv_mem hb⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact ha1 hmem
    have hle_a : stab P (a * b) ≤ stab P a := by
      intro p hp
      have hp' : (p • a) * (p • b) = a * b := by rw [← smul_mul', hp]
      exact (eq_of_mul_eq_mul_of_inf_eq_bot hinf ((hinv₁ p a).mp ha) ha
        ((hinv₂ p b).mp hb) hb hp').1
    have hc1 : Nat.card (stab P a) = Nat.card (stab P (a * b)) := hconst a (a * b) ha1 hab
    have h1 : stab P (a * b) = stab P a :=
      Subgroup.eq_of_le_of_card_ge hle_a (le_of_eq hc1)
    have hle_b : stab P (a * b) ≤ stab P b := by
      intro p hp
      have hp' : (p • a) * (p • b) = a * b := by rw [← smul_mul', hp]
      exact (eq_of_mul_eq_mul_of_inf_eq_bot hinf ((hinv₁ p a).mp ha) ha
        ((hinv₂ p b).mp hb) hb hp').2
    have hc2 : Nat.card (stab P b) = Nat.card (stab P (a * b)) := hconst b (a * b) hb1 hab
    have h2 : stab P (a * b) = stab P b :=
      Subgroup.eq_of_le_of_card_ge hle_b (le_of_eq hc2)
    rw [← h1, h2]
  -- a nonidentity element of each factor
  haveI hntE₁ : Nontrivial ↥E₁ := (Subgroup.nontrivial_iff_ne_bot E₁).mpr hnt₁
  obtain ⟨a₀, ha₀, ha₀ne⟩ : ∃ a ∈ E₁, a ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥E₁)
    exact ⟨(x : E), x.2, fun h => hx (Subtype.ext h)⟩
  haveI hntE₂ : Nontrivial ↥E₂ := (Subgroup.nontrivial_iff_ne_bot E₂).mpr hnt₂
  obtain ⟨b₀, hb₀, hb₀ne⟩ : ∃ b ∈ E₂, b ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥E₂)
    exact ⟨(x : E), x.2, fun h => hx (Subtype.ext h)⟩
  have key₁ : ∀ u ∈ E₁, u ≠ 1 → stab P u = stab P a₀ := by
    intro u hu hu1
    rw [key u hu hu1 b₀ hb₀ hb₀ne, key a₀ ha₀ ha₀ne b₀ hb₀ hb₀ne]
  have key₂ : ∀ v ∈ E₂, v ≠ 1 → stab P v = stab P a₀ := by
    intro v hv hv1
    rw [← key a₀ ha₀ ha₀ne v hv hv1]
  -- every element of `stab a₀` fixes all of `E`
  have hfix : ∀ p ∈ stab P a₀, ∀ x : E, p • x = x := by
    intro p hp x
    have h1 : E₁ ≤ fixSub P p := by
      intro u hu
      rcases eq_or_ne u 1 with rfl | hune
      · show p • (1 : E) = 1
        rw [smul_one]
      · have hp' : p ∈ stab P a₀ := hp
        rw [← key₁ u hu hune] at hp'
        exact hp'
    have h2 : E₂ ≤ fixSub P p := by
      intro v hv
      rcases eq_or_ne v 1 with rfl | hvne
      · show p • (1 : E) = 1
        rw [smul_one]
      · have hp' : p ∈ stab P a₀ := hp
        rw [← key₂ v hv hvne] at hp'
        exact hp'
    have h3 : E₁ ⊔ E₂ ≤ fixSub P p := sup_le h1 h2
    rw [hsup] at h3
    exact h3 trivial
  have hbot : stab P a₀ = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    exact hfaith p (fun x => hfix p hp x)
  have hcard0 : Nat.card (stab P a₀) = 1 := by
    rw [hbot, Subgroup.card_bot]
  intro p hpne a ha
  by_contra hane
  have hcard1 : Nat.card (stab P a) = 1 := by rw [hconst a a₀ hane ha₀ne, hcard0]
  have hbot' : stab P a = ⊥ := (Subgroup.card_eq_one).mp hcard1
  have : p ∈ stab P a := ha
  rw [hbot', Subgroup.mem_bot] at this
  exact hpne this

end DirectProduct

/-! ## Fixed points and commutators for the Appendix X lemma

For an action of a group `P` on an abelian group `E` through `ρ : P →* MulAut E` and a subgroup
`U ≤ P` we let `Cfix ρ U = C_E(U)` be the fixed-point subgroup and `Ccmt ρ U = [E,U]` the
subgroup generated by the commutators `e⁻¹ * ρ u e`.  The coprime-action decomposition
`E = C_E(U) · [E,U]` (the workspace lemma `Work.Coprime.abelian_split`) is the main tool. -/

section AppXSetup

variable {P E : Type*} [Group P] [Group E]

/-- `C_E(U)`: the fixed points in `E` of the subgroup `U ≤ P` acting through `ρ`. -/
def Cfix (ρ : P →* MulAut E) (U : Subgroup P) : Subgroup E :=
  { carrier := {e : E | ∀ u ∈ U, (ρ u) e = e}
    mul_mem' := by
      intro x y hx hy u hu
      rw [map_mul, hx u hu, hy u hu]
    one_mem' := by
      intro u _
      rw [map_one]
    inv_mem' := by
      intro x hx u hu
      rw [map_inv, hx u hu] }

@[simp] theorem mem_Cfix {ρ : P →* MulAut E} {U : Subgroup P} {e : E} :
    e ∈ Cfix ρ U ↔ ∀ u ∈ U, (ρ u) e = e := Iff.rfl

/-- `[E,U]`: the subgroup of `E` generated by the commutators `e⁻¹ * ρ u e`, `u ∈ U`. -/
def Ccmt (ρ : P →* MulAut E) (U : Subgroup P) : Subgroup E :=
  Subgroup.closure {y : E | ∃ u ∈ U, ∃ e : E, y = e⁻¹ * (ρ u) e}

theorem le_Ccmt {ρ : P →* MulAut E} {U : Subgroup P} {u : P} (hu : u ∈ U) (e : E) :
    e⁻¹ * (ρ u) e ∈ Ccmt ρ U :=
  Subgroup.subset_closure ⟨u, hu, e, rfl⟩

/-- If `t⁻¹ U t ⊆ U`, then `ρ t` preserves the fixed points of `U`. -/
theorem Cfix_smul_mem {ρ : P →* MulAut E} {U : Subgroup P} {t : P}
    (hnorm : ∀ u ∈ U, t⁻¹ * u * t ∈ U) {e : E} (he : e ∈ Cfix ρ U) :
    (ρ t) e ∈ Cfix ρ U := by
  intro u hu
  have h1 : (ρ u) ((ρ t) e) = (ρ (u * t)) e := by rw [map_mul, MulAut.mul_apply]
  have h2 : u * t = t * (t⁻¹ * u * t) := by group
  rw [h1, h2, map_mul, MulAut.mul_apply, he (t⁻¹ * u * t) (hnorm u hu)]

/-- If `t U t⁻¹ ⊆ U`, then `ρ t` preserves `[E,U]`. -/
theorem Ccmt_smul_mem {ρ : P →* MulAut E} {U : Subgroup P} {t : P}
    (hnorm : ∀ u ∈ U, t * u * t⁻¹ ∈ U) {e : E} (he : e ∈ Ccmt ρ U) :
    (ρ t) e ∈ Ccmt ρ U := by
  have hgen : ∀ y ∈ ({y : E | ∃ u ∈ U, ∃ e : E, y = e⁻¹ * (ρ u) e} : Set E),
      (ρ t) y ∈ Ccmt ρ U := by
    rintro y ⟨u, hu, e, rfl⟩
    refine Subgroup.subset_closure ⟨t * u * t⁻¹, hnorm u hu, (ρ t) e, ?_⟩
    show (ρ t) (e⁻¹ * (ρ u) e) = ((ρ t) e)⁻¹ * (ρ (t * u * t⁻¹)) ((ρ t) e)
    rw [map_mul, map_inv]
    congr 1
    have hg : (t * u * t⁻¹) * t = t * u := by group
    calc (ρ t) ((ρ u) e) = (ρ t * ρ u) e := (MulAut.mul_apply E (ρ t) (ρ u) e).symm
      _ = (ρ (t * u)) e := by rw [map_mul]
      _ = (ρ ((t * u * t⁻¹) * t)) e := by rw [hg]
      _ = (ρ (t * u * t⁻¹) * ρ t) e := by rw [map_mul]
      _ = (ρ (t * u * t⁻¹)) ((ρ t) e) := MulAut.mul_apply E (ρ (t * u * t⁻¹)) (ρ t) e
  have hsub : Subgroup.closure {y : E | ∃ u ∈ U, ∃ e : E, y = e⁻¹ * (ρ u) e} ≤
      (Ccmt ρ U).comap (ρ t).toMonoidHom :=
    (Subgroup.closure_le ((Ccmt ρ U).comap (ρ t).toMonoidHom)).mpr hgen
  rw [Ccmt] at he ⊢
  exact hsub he

/-- **The coprime-action decomposition.**  If `(Nat.card U, Nat.card E) = 1` and `E` is abelian,
then `E` is the direct product `C_E(U) × [E,U]`. -/
theorem Cfix_isComplement_Ccmt {ρ : P →* MulAut E} [Finite P] [Finite E] [IsMulCommutative E]
    (U : Subgroup P) (hcop : (Nat.card ↥U).Coprime (Nat.card E)) :
    (Cfix ρ U).IsComplement' (Ccmt ρ U) := by
  letI : MulDistribMulAction ↥U E := MulDistribMulAction.compHom E (ρ.comp U.subtype)
  have h := Work.Coprime.abelian_split ↥U hcop
  have h1 : FT.fixedPoints ↥U E = Cfix ρ U := by
    ext e
    constructor
    · intro h u hu
      exact h ⟨u, hu⟩
    · intro h u
      exact h u.1 u.2
  have h2 : FT.commutator ↥U (⊤ : Subgroup E) = Ccmt ρ U := by
    rw [Work.Coprime.commutator_eq_closure, Ccmt]
    congr 1
    ext y
    constructor
    · rintro ⟨a, x, -, rfl⟩
      exact ⟨a.1, a.2, x, rfl⟩
    · rintro ⟨u, hu, x, rfl⟩
      exact ⟨⟨u, hu⟩, x, Subgroup.mem_top x, rfl⟩
  rwa [h1, h2] at h

/-- **The key inclusion.**  Let `T, U ≤ P` commute and suppose `C_E(T) ⊓ C_E(U) = ⊥`.  If the
action of `U` on `E` is coprime, then every element of `C_E(T)` lies in `[E,U]`. -/
theorem Cfix_le_Ccmt_of_inf_eq_bot {ρ : P →* MulAut E} [Finite P] [Finite E] [IsMulCommutative E]
    {T U : Subgroup P} (hcop : (Nat.card ↥U).Coprime (Nat.card E))
    (hcomm : ∀ t ∈ T, ∀ u ∈ U, t * u = u * t) (hinf : Cfix ρ U ⊓ Cfix ρ T = ⊥) :
    Cfix ρ T ≤ Ccmt ρ U := by
  classical
  have hsplit : (Cfix ρ U).IsComplement' (Ccmt ρ U) := Cfix_isComplement_Ccmt U hcop
  have hc : Subgroup.IsComplement (Cfix ρ U : Set E) (Ccmt ρ U : Set E) :=
    Subgroup.isComplement'_def.mp hsplit
  have hex : ∀ e : E, ∃! x : ↥(Cfix ρ U) × ↥(Ccmt ρ U), (x.1 : E) * (x.2 : E) = e :=
    Subgroup.isComplement_iff_existsUnique.mp hc
  intro e he
  obtain ⟨x, hx, huniq⟩ := hex e
  have hx1 : (x.1 : E) ∈ Cfix ρ T := by
    intro t ht
    have h1 : (ρ t) (x.1 : E) ∈ Cfix ρ U :=
      Cfix_smul_mem (fun u hu => by
        rw [show t⁻¹ * u * t = u by
          rw [mul_assoc, ← hcomm t ht u hu, ← mul_assoc, inv_mul_cancel, one_mul]]; exact hu) x.1.2
    have h2 : (ρ t) (x.2 : E) ∈ Ccmt ρ U :=
      Ccmt_smul_mem (fun u hu => by
        rw [show t * u * t⁻¹ = u by
          rw [hcomm t ht u hu, mul_assoc, mul_inv_cancel, mul_one]]; exact hu) x.2.2
    have h3 : ((⟨(ρ t) (x.1 : E), h1⟩ : ↥(Cfix ρ U)),
        (⟨(ρ t) (x.2 : E), h2⟩ : ↥(Ccmt ρ U))) = x := by
      refine huniq _ ?_
      show (ρ t) (x.1 : E) * (ρ t) (x.2 : E) = e
      rw [← map_mul, hx, he t ht]
    exact congrArg (fun y : ↥(Cfix ρ U) × ↥(Ccmt ρ U) =>
      ((y.1 : ↥(Cfix ρ U)) : E)) h3
  have hx1bot : (x.1 : E) ∈ (⊥ : Subgroup E) := by
    rw [← hinf]; exact ⟨x.1.2, hx1⟩
  rw [Subgroup.mem_bot] at hx1bot
  have : e = (x.2 : E) := by rw [← hx, hx1bot, one_mul]
  rw [this]
  exact x.2.2

/-- `u X u⁻¹`, the conjugate of the subgroup `X` by `u`. -/
def Cconj (u : P) (X : Subgroup P) : Subgroup P := X.map (MulAut.conj u).toMonoidHom

theorem mem_Cconj {u : P} {X : Subgroup P} {y : P} :
    y ∈ Cconj u X ↔ ∃ x ∈ X, u * x * u⁻¹ = y := by
  rw [Cconj, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, MulAut.conj_apply u x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (MulAut.conj_apply u x).symm⟩

theorem Cconj_conj {u v : P} {X : Subgroup P} : Cconj u (Cconj v X) = Cconj (u * v) X := by
  rw [Cconj, Cconj, Cconj, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem Cconj_one {X : Subgroup P} : Cconj 1 X = X := by
  rw [Cconj]
  convert Subgroup.map_id X using 2
  ext x
  simp

theorem card_Cconj {u : P} {X : Subgroup P} : Nat.card ↥(Cconj u X) = Nat.card ↥X := by
  rw [Cconj]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective X (MulAut.conj u).toMonoidHom
    (MulAut.conj u).injective).toEquiv).symm

theorem Cconj_mono {u : P} {X Y : Subgroup P} (h : X ≤ Y) : Cconj u X ≤ Cconj u Y := by
  rw [Cconj, Cconj]
  exact Subgroup.map_mono h

theorem mem_Cconj_iff {u : P} {X : Subgroup P} {x : P} (hx : x ∈ X) : Cconj u X = X →
    u * x * u⁻¹ ∈ X := by
  intro h
  rw [← h]
  exact mem_Cconj.mpr ⟨x, hx, rfl⟩

/-- The stabiliser of a point of `E` in the acting group, as a subgroup of `P`. -/
def Pistab (ρ : P →* MulAut E) (e : E) : Subgroup P :=
  { carrier := {a : P | (ρ a) e = e}
    mul_mem' := by
      intro x y hx hy
      show (ρ (x * y)) e = e
      rw [map_mul]
      show (ρ x) ((ρ y) e) = e
      rw [hy, hx]
    one_mem' := by
      show (ρ 1) e = e
      rw [map_one]; rfl
    inv_mem' := by
      intro x hx
      show (ρ x⁻¹) e = e
      rw [map_inv]
      show ((ρ x)⁻¹) e = e
      have h1 : ((ρ x)⁻¹ : MulAut E) ((ρ x) e) = e := by
        rw [← MulAut.mul_apply E _ _ _, inv_mul_cancel]
        rfl
      rw [hx] at h1
      exact h1 }

@[simp] theorem mem_Pistab {ρ : P →* MulAut E} {e : E} {a : P} :
    a ∈ Pistab ρ e ↔ (ρ a) e = e := Iff.rfl

theorem Cfix_antitone {ρ : P →* MulAut E} {X Y : Subgroup P} (h : X ≤ Y) :
    Cfix ρ Y ≤ Cfix ρ X := fun e he x hx => he x (h hx)

theorem Cfix_sup {ρ : P →* MulAut E} (X Y : Subgroup P) :
    Cfix ρ (X ⊔ Y) = Cfix ρ X ⊓ Cfix ρ Y := by
  refine le_antisymm ?_ ?_
  · intro e he
    exact ⟨fun x hx => he x (Subgroup.mem_sup_left hx), fun y hy => he y (Subgroup.mem_sup_right hy)⟩
  · intro e he
    obtain ⟨he1, he2⟩ := Subgroup.mem_inf.mp he
    intro z hz
    have hsub : ((X : Set P) ∪ (Y : Set P)) ⊆ (Pistab ρ e : Set P) := by
      rintro a (ha | ha)
      · exact he1 a ha
      · exact he2 a ha
    have hcl : Subgroup.closure ((X : Set P) ∪ (Y : Set P)) ≤ Pistab ρ e :=
      (Subgroup.closure_le _).mpr hsub
    have hz' : z ∈ Subgroup.closure ((X : Set P) ∪ (Y : Set P)) := by
      rwa [← Subgroup.sup_eq_closure]
    exact hcl hz'

theorem Cfix_conj_mem {ρ : P →* MulAut E} {X : Subgroup P} {u : P} {e : E}
    (he : e ∈ Cfix ρ X) : (ρ u) e ∈ Cfix ρ (Cconj u X) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_Cconj.mp hy
  show (ρ (u * x * u⁻¹)) ((ρ u) e) = (ρ u) e
  have h1 : (ρ (u * x * u⁻¹)) ((ρ u) e) = (ρ ((u * x * u⁻¹) * u)) e := by
    rw [← MulAut.mul_apply E _ _ _, ← map_mul]
  rw [h1, show (u * x * u⁻¹) * u = u * x by group, map_mul, MulAut.mul_apply]
  exact congrArg (ρ u) (he x hx)

theorem Ccmt_conj_mem {ρ : P →* MulAut E} {X : Subgroup P} {u : P} {e : E}
    (he : e ∈ Ccmt ρ X) : (ρ u) e ∈ Ccmt ρ (Cconj u X) := by
  rw [Ccmt] at he ⊢
  have hgen : ∀ y ∈ ({y : E | ∃ x ∈ X, ∃ e : E, y = e⁻¹ * (ρ x) e} : Set E),
      (ρ u) y ∈ Subgroup.closure {y : E | ∃ x ∈ Cconj u X, ∃ e : E, y = e⁻¹ * (ρ x) e} := by
    rintro y ⟨x, hx, e, rfl⟩
    refine Subgroup.subset_closure ⟨u * x * u⁻¹, mem_Cconj.mpr ⟨x, hx, rfl⟩, (ρ u) e, ?_⟩
    show (ρ u) (e⁻¹ * (ρ x) e) = ((ρ u) e)⁻¹ * (ρ (u * x * u⁻¹)) ((ρ u) e)
    rw [map_mul, map_inv]
    congr 1
    have h1 : (ρ (u * x * u⁻¹)) ((ρ u) e) = (ρ ((u * x * u⁻¹) * u)) e := by
      rw [← MulAut.mul_apply E _ _ _, ← map_mul]
    rw [h1, show (u * x * u⁻¹) * u = u * x by group, map_mul, MulAut.mul_apply]
  exact ((Subgroup.closure_le
    ((Subgroup.closure {y : E | ∃ x ∈ Cconj u X, ∃ e : E, y = e⁻¹ * (ρ x) e}).comap
      (ρ u).toMonoidHom)).mpr hgen) he

theorem Cfix_inf_Ccmt {ρ : P →* MulAut E} [Finite P] [Finite E] [IsMulCommutative E]
    (X : Subgroup P) (hcop : (Nat.card ↥X).Coprime (Nat.card E)) :
    Cfix ρ X ⊓ Ccmt ρ X = ⊥ := by
  have h := (Cfix_isComplement_Ccmt (ρ := ρ) X hcop).disjoint
  rwa [disjoint_iff_inf_le, le_bot_iff] at h

/-- If `X ⊔ Y = R` with `C_E(R) = 1` and `X, Y` commute, then `C_E(X) ⊆ [E,Y]`. -/
theorem Cfix_le_Ccmt_of_sup_eq {ρ : P →* MulAut E} [Finite P] [Finite E] [IsMulCommutative E]
    {R X Y : Subgroup P} (hR : Cfix ρ R = ⊥) (hgen : X ⊔ Y = R)
    (hcop : (Nat.card ↥Y).Coprime (Nat.card E))
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : Cfix ρ X ≤ Ccmt ρ Y := by
  refine Cfix_le_Ccmt_of_inf_eq_bot hcop hcomm ?_
  rw [← Cfix_sup Y X, sup_comm, hgen, hR]

/-- **No `u` of odd order swaps two distinct subgroups.** -/
theorem no_conj_swap {G : Type*} [Group G] {u : G} (hodd : Odd (orderOf u)) {X Y : Subgroup G}
    (hX : Cconj u X = Y) (hY : Cconj u Y = X) (hne : X ≠ Y) : False := by
  obtain ⟨k, hk⟩ := hodd
  have hsq : Cconj (u ^ 2) X = X := by rw [pow_two, ← Cconj_conj, hX, hY]
  have heven : ∀ k : ℕ, Cconj (u ^ (2 * k)) X = X := by
    intro k
    induction k with
    | zero => rw [Nat.mul_zero, pow_zero, Cconj_one]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, ← Cconj_conj, ih, hsq]
  have h1 : Cconj (u ^ (2 * k + 1)) X = Y := by
    rw [pow_succ', ← Cconj_conj, heven k, hX]
  have h2 : Cconj (u ^ (2 * k + 1)) X = X := by
    rw [← hk, pow_orderOf_eq_one, Cconj_one]
  rw [h2] at h1
  exact hne h1

/-- Two distinct subgroups of order `p` of a subgroup of order `p ^ 2` generate it. -/
theorem sup_eq_of_card_eq_of_ne {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {R X Y : Subgroup G} (hR : Nat.card ↥R = p ^ 2) (hX : Nat.card ↥X = p)
    (hY : Nat.card ↥Y = p) (hXR : X ≤ R) (hYR : Y ≤ R) (hne : X ≠ Y) : X ⊔ Y = R := by
  have hle : X ⊔ Y ≤ R := sup_le hXR hYR
  have hlt : Nat.card ↥(X ⊔ Y) ≠ p := by
    intro hcon
    have h1 : X = X ⊔ Y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcon, hX])
    have h2 : Y ≤ X := h1 ▸ le_sup_right
    exact hne (Subgroup.eq_of_le_of_card_ge h2 (by rw [hY, hX])).symm
  have hdvd : Nat.card ↥(X ⊔ Y) ∣ p ^ 2 := by
    rw [← hR]; exact Subgroup.card_dvd_of_le hle
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hcardle : Nat.card ↥X ≤ Nat.card ↥(X ⊔ Y) :=
    Nat.card_le_card_of_injective
      (fun x : ↥X => (⟨x.1, Subgroup.mem_sup_left x.2⟩ : ↥(X ⊔ Y)))
      (fun a b h => Subtype.ext (congrArg (fun y : ↥(X ⊔ Y) => (y : G)) h))
  have hp2 : 2 ≤ p := hp.two_le
  have hge : 1 ≤ j := by
    have h1 : p ≤ p ^ j := by
      calc p = Nat.card ↥X := hX.symm
        _ ≤ Nat.card ↥(X ⊔ Y) := hcardle
        _ = p ^ j := hj
    by_contra hcon
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero] at h1
    omega
  have hne1 : j ≠ 1 := by
    intro hcon
    exact hlt (by rw [hj, hcon, pow_one])
  have hj2 : j = 2 := by omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hR, hj, hj2]

end AppXSetup

section AppXProp

/-- **The case `C_E(R) = 1` of the Appendix X Lemma.**  Here `R ⊴ P` is elementary abelian of
order `p ^ 2` with `p` odd and acts without fixed points; this leads to a contradiction. -/
private theorem appX_beta {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E] [IsMulCommutative E] [Nontrivial E]
    (ρ : P →* MulAut E) (hfaith : Function.Injective ρ)
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card {x : P | (ρ x) a = a} = Nat.card {y : P | (ρ y) b = b})
    (hcop : (Nat.card P).Coprime (Nat.card E))
    (hPp : IsPGroup p P)
    {R : Subgroup P} (hRnorm : R.Normal) (hRea : Work.PGroup.IsElementaryAbelian p R)
    (hRcard : Nat.card ↥R = p ^ 2) (hCR : Cfix ρ R = ⊥) : False := by
  classical
  letI : MulDistribMulAction P E := MulDistribMulAction.compHom E ρ
  haveI : Fact p.Prime := ⟨hp⟩
  have hfaith' : ∀ u : P, (∀ e : E, u • e = e) → u = 1 := fun u hu =>
    hfaith (by rw [map_one]; exact MulEquiv.ext fun e => hu e)
  have hRcomm : IsMulCommutative ↥R := hRea.1
  have hRexp : ∀ x : ↥R, x ^ p = 1 := hRea.2
  have hcommRR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp hRcomm ⟨x, hx⟩ ⟨y, hy⟩)
  -- every element of `P` has odd order
  have hoddP : ∀ u : P, Odd (orderOf u) := by
    intro u
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have h1 : orderOf u ∣ p ^ k := by rw [← hk]; exact orderOf_dvd_natCard u
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    rw [hj]
    exact Odd.pow hodd
  -- an element of `R` of order `p`
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    have h7 : 2 ≤ p := hp.two_le
    nlinarith [hRcard, h7]
  haveI hRnt : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  -- **the action of `R` is not fixed-point-free** (else `R` would be cyclic)
  have hRfpf_false : (∀ x : ↥R, x ≠ 1 → ∀ a : E, (ρ x.1) a = a → a = 1) → False := by
    intro hfpf
    have h1 : IsCyclic ↥R :=
      Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hp (hPp.to_subgroup R)
        (ρ.comp R.subtype) hfpf
    obtain ⟨r, hr⟩ := isCyclic_iff_exists_zpowers_eq_top.mp h1
    have h2 : orderOf r ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hRexp r)
    have h3 : orderOf r ≤ p := Nat.le_of_dvd hp.pos h2
    have h4 : Nat.card ↥R ≤ p := by
      have h5 : Nat.card ↥R = Nat.card ↥(Subgroup.zpowers r) := by
        rw [hr]
        exact (Nat.card_congr (Subgroup.topEquiv (G := ↥R)).toEquiv).symm
      rw [h5, Nat.card_zpowers]
      exact h3
    have h6 : p * p ≤ p := by rw [← pow_two, ← hRcard]; exact h4
    have h7 : 2 ≤ p := hp.two_le
    nlinarith [h6, h7]
  -- **`P` cannot act fixed-point-freely**
  have hfpf_false : (∀ x : P, x ≠ 1 → ∀ a : E, (ρ x) a = a → a = 1) → False :=
    fun hfpf => hRfpf_false (fun x hx a ha => hfpf x.1 (fun h => hx (Subtype.ext h)) a ha)
  -- **central elements act fixed-point-freely**
  have hZfix : ∀ z : P, z ∈ Subgroup.center P → z ≠ 1 → ∀ a : E, (ρ z) a = a → a = 1 := by
    intro z hz hz1 a ha
    by_contra hane
    have hZcop : (Nat.card ↥(Subgroup.zpowers z)).Coprime (Nat.card E) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) hcop
    have hnt1 : Cfix ρ (Subgroup.zpowers z) ≠ ⊥ := by
      intro hbot
      have hmem : a ∈ Cfix ρ (Subgroup.zpowers z) := fun t ht =>
        (Subgroup.zpowers_le (H := Pistab ρ a)).mpr ha ht
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hane hmem
    have hnt2 : Ccmt ρ (Subgroup.zpowers z) ≠ ⊥ := by
      intro hbot
      obtain ⟨e, he⟩ : ∃ e, (ρ z) e ≠ e := by
        by_contra h
        push Not at h
        exact hz1 (hfaith (by rw [map_one]; exact MulEquiv.ext h))
      have hmem : e⁻¹ * (ρ z) e ∈ Ccmt ρ (Subgroup.zpowers z) :=
        le_Ccmt (Subgroup.mem_zpowers z) e
      rw [hbot, Subgroup.mem_bot] at hmem
      exact he (by
        have h3 := congrArg (fun y => e * y) hmem
        simpa [mul_assoc] using h3)
    have hcen : ∀ a' ∈ Subgroup.zpowers z, ∀ u : P, u⁻¹ * a' * u = a' := by
      intro a' ha' u
      have hc := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hz ha') u
      rw [show u⁻¹ * a' * u = a' by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]]
    have hcen2 : ∀ a' ∈ Subgroup.zpowers z, ∀ u : P, u * a' * u⁻¹ = a' := by
      intro a' ha' u
      have hc := Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hz ha') u
      rw [show u * a' * u⁻¹ = a' by rw [hc, mul_assoc, mul_inv_cancel, mul_one]]
    have hinv1 : ∀ u : P, ∀ y : E, y ∈ Cfix ρ (Subgroup.zpowers z) ↔
        u • y ∈ Cfix ρ (Subgroup.zpowers z) := by
      intro u y
      constructor
      · intro hy
        exact Cfix_smul_mem (fun a' ha' => by rw [hcen a' ha' u]; exact ha') hy
      · intro hy
        have h1 : (ρ u⁻¹) ((ρ u) y) ∈ Cfix ρ (Subgroup.zpowers z) :=
          Cfix_smul_mem (t := u⁻¹) (fun a' ha' => by
            show (u⁻¹)⁻¹ * a' * u⁻¹ ∈ Subgroup.zpowers z
            rw [inv_inv, hcen2 a' ha' u]
            exact ha') hy
        rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
          MulAut.one_apply] at h1
    have hinv2 : ∀ u : P, ∀ y : E, y ∈ Ccmt ρ (Subgroup.zpowers z) ↔
        u • y ∈ Ccmt ρ (Subgroup.zpowers z) := by
      intro u y
      constructor
      · intro hy
        exact Ccmt_smul_mem (fun a' ha' => by rw [hcen2 a' ha' u]; exact ha') hy
      · intro hy
        have h1 : (ρ u⁻¹) ((ρ u) y) ∈ Ccmt ρ (Subgroup.zpowers z) :=
          Ccmt_smul_mem (t := u⁻¹) (fun a' ha' => by
            show (u⁻¹) * a' * (u⁻¹)⁻¹ ∈ Subgroup.zpowers z
            rw [inv_inv, hcen a' ha' u]
            exact ha') hy
        rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
          MulAut.one_apply] at h1
    exact hfpf_false (fpf_of_directProduct (Cfix ρ (Subgroup.zpowers z))
      (Ccmt ρ (Subgroup.zpowers z)) (Cfix_inf_Ccmt _ hZcop)
      (Cfix_isComplement_Ccmt _ hZcop).sup_eq_top hnt1 hnt2 hinv1 hinv2 hfaith'
      (fun a' b' ha' hb' => hconst a' b' ha' hb'))
  -- ## a nonzero element fixed by a line of `R`
  have hex : ∃ (T : Subgroup P) (e : E), T ≤ R ∧ Nat.card ↥T = p ∧ e ∈ Cfix ρ T ∧ e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hRfpf_false
    intro x hx a ha
    have hline : Nat.card ↥(Subgroup.zpowers x.1) = p := by
      rw [Nat.card_zpowers]
      have h1 : orderOf x.1 ∣ p :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa using congrArg Subtype.val (hRexp x))
      rcases hp.eq_one_or_self_of_dvd _ h1 with h1' | h1'
      · have hx1 : x = 1 := Subtype.ext (by
          simpa using (orderOf_eq_one_iff.mp h1' : (x : P) = 1))
        exact absurd hx1 hx
      · exact h1'
    have hmem : a ∈ Cfix ρ (Subgroup.zpowers x.1) := fun t ht =>
      (Subgroup.zpowers_le (H := Pistab ρ a)).mpr ha ht
    exact hcon (Subgroup.zpowers x.1) a (Subgroup.zpowers_le.mpr x.2) hline hmem
  obtain ⟨T, e, hTR, hTcard, heT, he1⟩ := hex
  -- a nonidentity element of `T`
  have hTne : ∃ z ∈ T, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hTbot : T = ⊥ := by
      ext x
      simp only [Subgroup.mem_bot]
      exact ⟨hcon x, fun h => h ▸ T.one_mem⟩
    rw [hTbot, Subgroup.card_bot] at hTcard
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hcopT : (Nat.card ↥T).Coprime (Nat.card E) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card T) hcop
  have hcommTT' : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x :=
    fun x hx y hy => hcommRR x (hTR hx) y (hTR hy)
  -- **`T` is not central**
  have hTnotZ : ¬ T ≤ Subgroup.center P := by
    intro hTZ
    obtain ⟨z, hzT, hz1⟩ := hTne
    exact he1 (hZfix z (hTZ hzT) hz1 e (heT z hzT))
  -- **`T` is not normal in `P`**
  have hTnotNorm : ¬ T.Normal := by
    intro hTnorm
    have hconj : ∀ u : P, Cconj u T = T := by
      intro u
      refine le_antisymm ?_ ?_
      · rw [Cconj]
        rintro y ⟨x, hx, rfl⟩
        exact hTnorm.conj_mem x hx u
      · intro y hy
        refine mem_Cconj.mpr ⟨u⁻¹ * y * u, by simpa using hTnorm.conj_mem y hy u⁻¹, ?_⟩
        group
    have hnt1 : Cfix ρ T ≠ ⊥ := by
      intro hbot
      have hmem : e ∈ (⊥ : Subgroup E) := by rw [← hbot]; exact heT
      rw [Subgroup.mem_bot] at hmem
      exact he1 hmem
    have hnt2 : Ccmt ρ T ≠ ⊥ := by
      obtain ⟨z, hzT, hz1⟩ := hTne
      intro hbot
      obtain ⟨y, hy⟩ : ∃ y, (ρ z) y ≠ y := by
        by_contra h
        push Not at h
        exact hz1 (hfaith (by rw [map_one]; exact MulEquiv.ext h))
      have hmem : y⁻¹ * (ρ z) y ∈ Ccmt ρ T := le_Ccmt hzT y
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hy (by
        have h3 := congrArg (fun w => y * w) hmem
        simpa [mul_assoc] using h3)
    have hinv1 : ∀ u : P, ∀ y : E, y ∈ Cfix ρ T ↔ u • y ∈ Cfix ρ T := by
      intro u y
      constructor
      · intro hy
        have h := Cfix_conj_mem (u := u) hy
        rwa [hconj u] at h
      · intro hy
        have h := Cfix_conj_mem (u := u⁻¹) hy
        rw [show (ρ u⁻¹) (u • y) = y from by
          show (ρ u⁻¹) ((ρ u) y) = y
          rw [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
            MulAut.one_apply]] at h
        rwa [hconj u⁻¹] at h
    have hinv2 : ∀ u : P, ∀ y : E, y ∈ Ccmt ρ T ↔ u • y ∈ Ccmt ρ T := by
      intro u y
      constructor
      · intro hy
        have h := Ccmt_conj_mem (u := u) hy
        rwa [hconj u] at h
      · intro hy
        have h := Ccmt_conj_mem (u := u⁻¹) hy
        rw [show (ρ u⁻¹) (u • y) = y from by
          show (ρ u⁻¹) ((ρ u) y) = y
          rw [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
            MulAut.one_apply]] at h
        rwa [hconj u⁻¹] at h
    have hf := fpf_of_directProduct (Cfix ρ T) (Ccmt ρ T) (Cfix_inf_Ccmt T hcopT)
      (Cfix_isComplement_Ccmt T hcopT).sup_eq_top hnt1 hnt2 hinv1 hinv2 hfaith'
      (fun a' b' ha' hb' => hconst a' b' ha' hb')
    exact hfpf_false hf
  -- take `u` with `u T u⁻¹ ≠ T`
  obtain ⟨u, huT⟩ : ∃ u : P, Cconj u T ≠ T := by
    by_contra hcon
    push Not at hcon
    exact hTnotNorm ⟨fun x hx g => by rw [← hcon g]; exact mem_Cconj.mpr ⟨x, hx, rfl⟩⟩
  set T' : Subgroup P := Cconj u T with hT'def
  have hT'R : T' ≤ R := by
    rw [hT'def, Cconj]
    rintro y ⟨x, hx, rfl⟩
    exact hRnorm.conj_mem x (hTR hx) u
  have hT'card : Nat.card ↥T' = p := by rw [hT'def, card_Cconj, hTcard]
  have hT'ne : T' ≠ T := by rw [hT'def]; exact huT
  have hgen : T ⊔ T' = R :=
    sup_eq_of_card_eq_of_ne hp hRcard hTcard hT'card hTR hT'R (Ne.symm hT'ne)
  set f : E := (ρ u) e with hfdef
  have hfT' : f ∈ Cfix ρ T' := by
    rw [hT'def, hfdef]; exact Cfix_conj_mem heT
  have hf1 : f ≠ 1 := by
    intro h
    exact he1 ((ρ u).injective (by rw [← hfdef, h, map_one]))
  have hcommTT'2 : ∀ x ∈ T, ∀ y ∈ T', x * y = y * x :=
    fun x hx y hy => hcommRR x (hTR hx) y (hT'R hy)
  have hfcmt : f ∈ Ccmt ρ T :=
    Cfix_le_Ccmt_of_sup_eq hCR (by rw [sup_comm]; exact hgen) hcopT
      (fun x hx y hy => hcommRR x (hT'R hx) y (hTR hy)) hfT'
  have hef1 : e * f ≠ 1 := by
    intro h
    have h2 : e = f⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have h3 : e ∈ Cfix ρ T ⊓ Cfix ρ T' :=
      ⟨heT, by rw [h2]; exact (Cfix ρ T').inv_mem hfT'⟩
    rw [← Cfix_sup, hgen, hCR, Subgroup.mem_bot] at h3
    exact he1 h3
  -- ## the core: elements fixing `e * f` fix `e` and `f`
  have hcore : ∀ v : P, (ρ v) (e * f) = e * f → (ρ v) e = e ∧ (ρ v) f = f := by
    intro v hv
    by_cases hvT : Cconj v T = T
    · -- `v` normalises `T`
      have hconjv : Cconj v⁻¹ T = T := by
        rw [show Cconj v⁻¹ T = Cconj v⁻¹ (Cconj v T) by rw [hvT],
          Cconj_conj, inv_mul_cancel, Cconj_one]
      have hinv1 : ∀ y : E, y ∈ Cfix ρ T ↔ (ρ v) y ∈ Cfix ρ T := by
        intro y
        constructor
        · intro hy
          have h := Cfix_conj_mem (u := v) hy
          rwa [hvT] at h
        · intro hy
          have h := Cfix_conj_mem (u := v⁻¹) hy
          rw [show (ρ v⁻¹) ((ρ v) y) = y from by
            rw [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
              MulAut.one_apply]] at h
          rwa [hconjv] at h
      have hinv2 : ∀ y : E, y ∈ Ccmt ρ T ↔ (ρ v) y ∈ Ccmt ρ T := by
        intro y
        constructor
        · intro hy
          have h := Ccmt_conj_mem (u := v) hy
          rwa [hvT] at h
        · intro hy
          have h := Ccmt_conj_mem (u := v⁻¹) hy
          rw [show (ρ v⁻¹) ((ρ v) y) = y from by
            rw [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one,
              MulAut.one_apply]] at h
          rwa [hconjv] at h
      have h1 : (ρ v) e ∈ Cfix ρ T := (hinv1 e).mp heT
      have h2 : (ρ v) f ∈ Ccmt ρ T := (hinv2 f).mp hfcmt
      have h3 : (ρ v) e * (ρ v) f = e * f := by rw [← map_mul]; exact hv
      exact eq_of_mul_eq_mul_of_inf_eq_bot (Cfix_inf_Ccmt T hcopT) h1 heT h2 hfcmt h3
    · -- `v` does not normalise `T`
      exfalso
      have hY_R : Cconj v T ≤ R := by
        rw [Cconj]
        rintro y ⟨x, hx, rfl⟩
        exact hRnorm.conj_mem x (hTR hx) v
      have hY_card : Nat.card ↥(Cconj v T) = p := by rw [card_Cconj, hTcard]
      have hYcop : (Nat.card ↥(Cconj v T)).Coprime (Nat.card E) :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) hcop
      have hve : (ρ v) e ∈ Cfix ρ (Cconj v T) := Cfix_conj_mem heT
      have hvf : (ρ v) f ∈ Ccmt ρ (Cconj v T) := Ccmt_conj_mem hfcmt
      by_cases hY : Cconj v T = T'
      · -- `v` maps `T` to `T'`: then `v` swaps `T` and `T'`
        have hecmt : e ∈ Ccmt ρ T' :=
          Cfix_le_Ccmt_of_sup_eq hCR hgen
            (Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card T') hcop)
            (fun x hx y hy => hcommRR x (hTR hx) y (hT'R hy)) heT
        have hEcomm : f * e = e * f := isMulCommutative_iff.mp inferInstance f e
        have h1 : f * e = (ρ v) e * (ρ v) f := by
          rw [hEcomm, show e * f = (ρ v) (e * f) from hv.symm, map_mul]
        have hve' : (ρ v) e ∈ Cfix ρ T' := by rw [← hY]; exact hve
        have hvf' : (ρ v) f ∈ Ccmt ρ T' := by rw [← hY]; exact hvf
        have hcopT' : (Nat.card ↥T').Coprime (Nat.card E) :=
          Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card T') hcop
        have huniq := eq_of_mul_eq_mul_of_inf_eq_bot (Cfix_inf_Ccmt T' hcopT')
          hfT' hve' hecmt hvf' h1
        have h2 : e ∈ Cfix ρ (Cconj v T') := by
          have hh := Cfix_conj_mem (u := v) hfT'
          rwa [← huniq.2] at hh
        have h3 : Cconj v T' = T := by
          by_contra hcon
          have hY'R : Cconj v T' ≤ R := by
            rw [Cconj]
            rintro y ⟨x, hx, rfl⟩
            exact hRnorm.conj_mem x (hT'R hx) v
          have hgen2 : T ⊔ Cconj v T' = R :=
            sup_eq_of_card_eq_of_ne hp hRcard hTcard (by rw [card_Cconj, hT'card])
              hTR hY'R (Ne.symm hcon)
          have h4 : e ∈ Cfix ρ R := by
            rw [← hgen2, Cfix_sup]
            exact ⟨heT, h2⟩
          rw [hCR, Subgroup.mem_bot] at h4
          exact he1 h4
        exact no_conj_swap (hoddP v) hY h3 (Ne.symm hT'ne)
      · -- `v T ∉ {T, T'}`: the component argument
        have hecmt : e ∈ Ccmt ρ (Cconj v T) :=
          Cfix_le_Ccmt_of_sup_eq hCR
            (sup_eq_of_card_eq_of_ne hp hRcard hTcard hY_card hTR hY_R (Ne.symm hvT))
            hYcop (fun x hx y hy => hcommRR x (hTR hx) y (hY_R hy)) heT
        have hfcmt' : f ∈ Ccmt ρ (Cconj v T) :=
          Cfix_le_Ccmt_of_sup_eq hCR
            (sup_eq_of_card_eq_of_ne hp hRcard hT'card hY_card hT'R hY_R (Ne.symm hY))
            hYcop (fun x hx y hy => hcommRR x (hT'R hx) y (hY_R hy)) hfT'
        have h1 : (ρ v) e * (ρ v) f = 1 * (e * f) := by
          rw [← map_mul, hv, one_mul]
        have huniq := eq_of_mul_eq_mul_of_inf_eq_bot (Cfix_inf_Ccmt (Cconj v T) hYcop)
          hve (Cfix ρ (Cconj v T)).one_mem hvf
          ((Ccmt ρ (Cconj v T)).mul_mem hecmt hfcmt') h1
        exact he1 ((ρ v).injective (by rw [huniq.1, map_one]))
  -- ## the constancy argument
  have hstab_le : Pistab ρ (e * f) ≤ Pistab ρ e := fun v hv => (hcore v hv).1
  have hstab_le' : Pistab ρ (e * f) ≤ Pistab ρ f := fun v hv => (hcore v hv).2
  have hcard_eq : Nat.card (Pistab ρ (e * f)) = Nat.card (Pistab ρ e) :=
    (hconst e (e * f) he1 hef1).symm
  have hcard_eq' : Nat.card (Pistab ρ (e * f)) = Nat.card (Pistab ρ f) :=
    (hconst f (e * f) hf1 hef1).symm
  have hstab_eq : Pistab ρ (e * f) = Pistab ρ e :=
    Subgroup.eq_of_le_of_card_ge hstab_le (le_of_eq hcard_eq.symm)
  have hstab_eq' : Pistab ρ (e * f) = Pistab ρ f :=
    Subgroup.eq_of_le_of_card_ge hstab_le' (le_of_eq hcard_eq'.symm)
  have hstab : Pistab ρ e = Pistab ρ f := hstab_eq.symm.trans hstab_eq'
  -- ## `R ∩ P_e = T` and `R ∩ P_f = T'`
  have hRstab : R ⊓ Pistab ρ e = T := by
    refine le_antisymm ?_ ?_
    · intro v hv
      obtain ⟨hvR, hve⟩ := Subgroup.mem_inf.mp hv
      by_contra hvTin
      have hv1 : v ≠ 1 := fun h => hvTin (h ▸ T.one_mem)
      have hline : Nat.card ↥(Subgroup.zpowers v) = p := by
        rw [Nat.card_zpowers]
        have h1 : orderOf v ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (by
          have h2 := hRexp ⟨v, hvR⟩
          simpa using congrArg Subtype.val h2)
        rcases hp.eq_one_or_self_of_dvd _ h1 with h1' | h1'
        · exact absurd h1' (fun h => hv1 (orderOf_eq_one_iff.mp h))
        · exact h1'
      have hzpne : Subgroup.zpowers v ≠ T := fun h => hvTin (h ▸ Subgroup.mem_zpowers v)
      have hgen2 : T ⊔ Subgroup.zpowers v = R :=
        sup_eq_of_card_eq_of_ne hp hRcard hTcard hline hTR (Subgroup.zpowers_le.mpr hvR)
          (Ne.symm hzpne)
      have h4 : e ∈ Cfix ρ R := by
        rw [← hgen2, Cfix_sup]
        exact ⟨heT, (Subgroup.zpowers_le (H := Pistab ρ e)).mpr hve⟩
      rw [hCR, Subgroup.mem_bot] at h4
      exact he1 h4
    · intro t ht
      exact Subgroup.mem_inf.mpr ⟨hTR ht, heT t ht⟩
  have hRstab' : R ⊓ Pistab ρ f = T' := by
    refine le_antisymm ?_ ?_
    · intro v hv
      obtain ⟨hvR, hvf⟩ := Subgroup.mem_inf.mp hv
      by_contra hvTin
      have hv1 : v ≠ 1 := fun h => hvTin (h ▸ T'.one_mem)
      have hline : Nat.card ↥(Subgroup.zpowers v) = p := by
        rw [Nat.card_zpowers]
        have h1 : orderOf v ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (by
          have h2 := hRexp ⟨v, hvR⟩
          simpa using congrArg Subtype.val h2)
        rcases hp.eq_one_or_self_of_dvd _ h1 with h1' | h1'
        · exact absurd h1' (fun h => hv1 (orderOf_eq_one_iff.mp h))
        · exact h1'
      have hzpne : Subgroup.zpowers v ≠ T' := fun h => hvTin (h ▸ Subgroup.mem_zpowers v)
      have hgen2 : T' ⊔ Subgroup.zpowers v = R :=
        sup_eq_of_card_eq_of_ne hp hRcard hT'card hline hT'R (Subgroup.zpowers_le.mpr hvR)
          (Ne.symm hzpne)
      have h4 : f ∈ Cfix ρ R := by
        rw [← hgen2, Cfix_sup]
        exact ⟨hfT', (Subgroup.zpowers_le (H := Pistab ρ f)).mpr hvf⟩
      rw [hCR, Subgroup.mem_bot] at h4
      exact hf1 h4
    · intro t ht
      exact Subgroup.mem_inf.mpr ⟨hT'R ht, hfT' t ht⟩
  exact hT'ne ((hRstab.symm.trans (hstab.symm ▸ hRstab')).symm)

end AppXProp

section AppXProp

/-- **The Lemma of Peterfalvi II, Appendix X (p. 281).**  Let `P` be a finite `p`-group (`p` odd)
acting faithfully and coprimely on a finite abelian group `E`, and suppose that the stabilisers of
all nonidentity elements of `E` have the same cardinality.  Then `P` is cyclic and acts
fixed-point-freely on `E`. -/
private theorem appX_prop {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E] [IsMulCommutative E]
    (hPp : IsPGroup p P) (hcop : (Nat.card P).Coprime (Nat.card E))
    (ρ : P →* MulAut E) (hfaith : Function.Injective ρ)
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card {x : P | (ρ x) a = a} = Nat.card {y : P | (ρ y) b = b}) :
    IsCyclic P ∧ ∀ x : P, x ≠ 1 → ∀ a : E, (ρ x) a = a → a = 1 := by
  classical
  letI : MulDistribMulAction P E := MulDistribMulAction.compHom E ρ
  have hfaith' : ∀ u : P, (∀ e : E, u • e = e) → u = 1 := fun u hu =>
    hfaith (by rw [map_one]; exact MulEquiv.ext fun e => hu e)
  rcases subsingleton_or_nontrivial P with hP1 | hPnt
  · haveI := hP1
    exact ⟨isCyclic_of_subsingleton, fun x hx _ _ => absurd (Subsingleton.elim x 1) hx⟩
  rcases subsingleton_or_nontrivial E with hE1 | hEnt
  · exfalso
    have hMA : Subsingleton (MulAut E) := ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact (not_subsingleton_iff_nontrivial.mpr hPnt)
      ⟨fun x y => hfaith (Subsingleton.elim (ρ x) (ρ y))⟩
  have hmoves : ∀ u : P, u ≠ 1 → ∃ e : E, (ρ u) e ≠ e := by
    intro u hu
    by_contra h
    push Not at h
    exact hu (hfaith' u h)
  -- ## The cyclic case
  by_cases hcyc : IsCyclic P
  · haveI : IsCyclic P := hcyc
    haveI hPcomm : IsMulCommutative P := inferInstance
    have hcommP : ∀ a b : P, a * b = b * a := isMulCommutative_iff.mp hPcomm
    refine ⟨hcyc, ?_⟩
    intro x hx a ha
    by_contra hane
    let A : Subgroup P := Subgroup.zpowers x
    have hAcop : (Nat.card ↥A).Coprime (Nat.card E) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card A) hcop
    have hsplit : (Cfix ρ A).IsComplement' (Ccmt ρ A) := Cfix_isComplement_Ccmt A hAcop
    have hinf : Cfix ρ A ⊓ Ccmt ρ A = ⊥ := by
      have hd := hsplit.disjoint
      rwa [disjoint_iff_inf_le, le_bot_iff] at hd
    have hnt₁ : Cfix ρ A ≠ ⊥ := by
      intro hbot
      have hmem : a ∈ Cfix ρ A := fun u hu =>
        (Subgroup.zpowers_le (H := stab P a)).mpr ha hu
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hane hmem
    have hnt₂ : Ccmt ρ A ≠ ⊥ := by
      intro hbot
      obtain ⟨e, he⟩ := hmoves x hx
      have hmem : e⁻¹ * (ρ x) e ∈ Ccmt ρ A := le_Ccmt (Subgroup.mem_zpowers x) e
      rw [hbot, Subgroup.mem_bot] at hmem
      exact he (by
        have h2 : e⁻¹ * (ρ x) e = 1 := hmem
        have h3 := congrArg (fun y => e * y) h2
        simpa [mul_assoc] using h3)
    have hinv₁ : ∀ u : P, ∀ e : E, e ∈ Cfix ρ A ↔ u • e ∈ Cfix ρ A := by
      intro u e
      constructor
      · intro he
        exact Cfix_smul_mem (fun a' ha' => by
          rw [show u⁻¹ * a' * u = a' by
            rw [mul_assoc, hcommP a' u, ← mul_assoc, inv_mul_cancel, one_mul]]; exact ha') he
      · intro he
        have h1 : (ρ u⁻¹) ((ρ u) e) ∈ Cfix ρ A :=
          Cfix_smul_mem (fun a' ha' => by
            show (u⁻¹)⁻¹ * a' * u⁻¹ ∈ A
            rw [inv_inv]
            rw [show u * a' * u⁻¹ = a' by
              rw [← hcommP a' u, mul_assoc, mul_inv_cancel, mul_one]]
            exact ha') he
        rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
    have hinv₂ : ∀ u : P, ∀ e : E, e ∈ Ccmt ρ A ↔ u • e ∈ Ccmt ρ A := by
      intro u e
      constructor
      · intro he
        exact Ccmt_smul_mem (fun a' ha' => by
          rw [show u * a' * u⁻¹ = a' by
            rw [← hcommP a' u, mul_assoc, mul_inv_cancel, mul_one]]; exact ha') he
      · intro he
        have h1 : (ρ u⁻¹) ((ρ u) e) ∈ Ccmt ρ A :=
          Ccmt_smul_mem (fun a' ha' => by
            rw [show u⁻¹ * a' * (u⁻¹)⁻¹ = a' by
              rw [inv_inv, mul_assoc, hcommP a' u, ← mul_assoc, inv_mul_cancel, one_mul]]
            exact ha') he
        rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
    have hfpf := fpf_of_directProduct (Cfix ρ A) (Ccmt ρ A) hinf hsplit.sup_eq_top hnt₁ hnt₂
      hinv₁ hinv₂ hfaith'
      (fun a' b' ha' hb' => hconst a' b' ha' hb')
    exact hane (hfpf x hx a ha)
  · -- ## The non-cyclic case
    exfalso
    -- a normal subgroup of type `(p,p)`
    obtain ⟨R, hRle, hRnorm, hRtype⟩ :=
      Work.PGroup.normal_typePP_of_not_isCyclic (G := P) hp hodd
        (P := (⊤ : Subgroup P)) (hPp.to_subgroup ⊤) (by
          intro h
          exact hcyc ((Subgroup.topEquiv (G := P)).isCyclic.mp h))
    haveI hRnormal : R.Normal := by
      have h2 := hRnorm.map (Subgroup.subtype (⊤ : Subgroup P))
        (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
      rwa [Subgroup.subgroupOf_map_subtype, inf_top_eq] at h2
    haveI hRcomm : IsMulCommutative ↥R := hRtype.1.1
    have hRexp : ∀ x : ↥R, x ^ p = 1 := hRtype.1.2
    have hRcard : Nat.card ↥R = p ^ 2 := hRtype.2
    have hRp : IsPGroup p ↥R := hPp.to_subgroup R
    have hRcop : (Nat.card ↥R).Coprime (Nat.card E) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card R) hcop
    -- the action is not fixed-point-free
    have notfpf : ¬ (∀ x : P, x ≠ 1 → ∀ a : E, (ρ x) a = a → a = 1) := by
      intro hfpf
      have hcycR : IsCyclic ↥R :=
        Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic hp hRp (ρ.comp R.subtype)
          (fun x hx a ha => hfpf x.1 (fun h => hx (Subtype.ext h)) a ha)
      obtain ⟨r, hr⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcycR
      have h1 : orderOf r ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hRexp r)
      have h2 : orderOf r ≤ p := Nat.le_of_dvd hp.pos h1
      have h3 : Nat.card ↥R ≤ p := by
        have h4 : Nat.card ↥R = Nat.card ↥(Subgroup.zpowers r) := by
          rw [hr]
          exact (Nat.card_congr (Subgroup.topEquiv (G := ↥R)).toEquiv).symm
        rw [h4, Nat.card_zpowers]
        exact h2
      have h4 : p * p ≤ p := by rw [← pow_two, ← hRcard]; exact h3
      have h5 : 2 ≤ p := hp.two_le
      nlinarith [h4, h5]
    by_cases hCR : Cfix ρ R = ⊥
    · -- ### Case `C_E(R) = 1`
      haveI : Nontrivial E := hEnt
      exact appX_beta hp hodd ρ hfaith hconst hcop hPp hRnormal hRtype.1 hRtype.2 hCR
    · -- ### Case `C_E(R) ≠ 1`
      have hsplit : (Cfix ρ R).IsComplement' (Ccmt ρ R) := Cfix_isComplement_Ccmt R hRcop
      have hinf : Cfix ρ R ⊓ Ccmt ρ R = ⊥ := by
        have hd := hsplit.disjoint
        rwa [disjoint_iff_inf_le, le_bot_iff] at hd
      have hRne : R ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hRcard
        have h5 : 2 ≤ p := hp.two_le
        nlinarith [hRcard, h5]
      haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
      have hnt₂ : Ccmt ρ R ≠ ⊥ := by
        intro hbot
        obtain ⟨r, hr⟩ := exists_ne (1 : ↥R)
        obtain ⟨e, he⟩ := hmoves r.1 (fun h => hr (Subtype.ext h))
        have hmem : e⁻¹ * (ρ r.1) e ∈ Ccmt ρ R := le_Ccmt r.2 e
        rw [hbot, Subgroup.mem_bot] at hmem
        exact he (by
          have h2 : e⁻¹ * (ρ r.1) e = 1 := hmem
          have h3 := congrArg (fun y => e * y) h2
          simpa [mul_assoc] using h3)
      have hinv₁ : ∀ u : P, ∀ e : E, e ∈ Cfix ρ R ↔ u • e ∈ Cfix ρ R := by
        intro u e
        constructor
        · intro he
          exact Cfix_smul_mem (fun a' ha' => by simpa using hRnormal.conj_mem a' ha' u⁻¹) he
        · intro he
          have h1 : (ρ u⁻¹) ((ρ u) e) ∈ Cfix ρ R :=
            Cfix_smul_mem (fun a' ha' => by simpa using hRnormal.conj_mem a' ha' u) he
          rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
      have hinv₂ : ∀ u : P, ∀ e : E, e ∈ Ccmt ρ R ↔ u • e ∈ Ccmt ρ R := by
        intro u e
        constructor
        · intro he
          exact Ccmt_smul_mem (fun a' ha' => by
            simpa using hRnormal.conj_mem a' ha' u) he
        · intro he
          have h1 : (ρ u⁻¹) ((ρ u) e) ∈ Ccmt ρ R :=
            Ccmt_smul_mem (fun a' ha' => by
              simpa using hRnormal.conj_mem a' ha' u⁻¹) he
          rwa [← MulAut.mul_apply E _ _ _, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
      have hfpf := fpf_of_directProduct (Cfix ρ R) (Ccmt ρ R) hinf hsplit.sup_eq_top hCR
        hnt₂ hinv₁ hinv₂ hfaith' (fun a' b' ha' hb' => hconst a' b' ha' hb')
      exact notfpf hfpf

end AppXProp

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem appX (hFT : FeitThompsonProp) {D E : Type} [Group D] [Finite D] [Group E] [Finite E] (hoddD : Odd (Nat.card D)) {p : ℕ} (hp : p.Prime) (hEab : ∀ x y : E, x * y = y * x) (hEexp : ∀ x : E, x ^ p = 1) (ρ : D →* MulAut E) (hfaith : Function.Injective ρ) (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) : IsCyclic ↥(Work.Fitting.fitting D) ∧ (∀ d ∈ Work.Fitting.fitting D, d ≠ 1 → ∀ a : E, ρ d a = a → a = 1) ∧ (∀ x y : D, x * y * x⁻¹ * y⁻¹ ∈ Work.Fitting.fitting D) := by
  classical
  haveI hEcomm : IsMulCommutative E := isMulCommutative_iff.mpr hEab
  rcases subsingleton_or_nontrivial E with hE1 | hEnt
  · -- ## Case `E` trivial: then `D` is trivial
    haveI := hE1
    have hSub : Subsingleton (MulAut E) :=
      ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    haveI : Subsingleton D := ⟨fun x y => hfaith (hSub.elim (ρ x) (ρ y))⟩
    haveI : Subsingleton ↥(Work.Fitting.fitting D) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨isCyclic_of_subsingleton, ?_, ?_⟩
    · intro d _ hd
      exact absurd (Subsingleton.elim d 1) hd
    · intro x y
      rw [Subsingleton.elim x 1, Subsingleton.elim y 1]
      simpa using (Work.Fitting.fitting D).one_mem
  · -- ## Case `E` nontrivial: `|E|` is a power of `2`
    haveI := hEnt
    obtain ⟨k, hk⟩ := appX_card_E hoddD hp hEab hEexp ρ hfaith htrans
    -- Every `O_ℓ(D)`, `ℓ` a prime divisor of `|D|`, is cyclic and acts fixed-point-freely.
    have key : ∀ ℓ ∈ (Nat.card D).primeFactors,
        IsCyclic ↥(Work.Fitting.pCore ℓ D) ∧
        (∀ x : ↥(Work.Fitting.pCore ℓ D), x ≠ 1 → ∀ a : E, (ρ x.1) a = a → a = 1) := by
      intro ℓ hℓ
      have hℓprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
      have hℓodd : Odd ℓ := by
        refine hℓprime.odd_of_ne_two ?_
        intro h2
        exact (Nat.not_even_iff_odd.mpr hoddD)
          (even_iff_two_dvd.mpr (h2 ▸ (Nat.mem_primeFactors.mp hℓ).2.1))
      -- `|O_ℓ(D)|` is a power of `ℓ`, `|E|` a power of `2`, and `ℓ` is odd: coprime
      have hcop : (Nat.card ↥(Work.Fitting.pCore ℓ D)).Coprime (Nat.card E) := by
        haveI : Fact ℓ.Prime := ⟨hℓprime⟩
        obtain ⟨n, hn⟩ := (Work.Fitting.isPGroup_pCore (G := D) hℓprime).exists_card_eq
        rw [hn, hk]
        exact Nat.Coprime.pow_left n (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hℓodd))
      -- the stabilisers of all nonidentity elements have the same cardinality
      have hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
          Nat.card {x : ↥(Work.Fitting.pCore ℓ D) |
            ((ρ.comp (Work.Fitting.pCore ℓ D).subtype) x) a = a} =
          Nat.card {y : ↥(Work.Fitting.pCore ℓ D) |
            ((ρ.comp (Work.Fitting.pCore ℓ D).subtype) y) b = b} := by
        intro a b ha hb
        obtain ⟨d, hd⟩ := htrans a b ha hb
        haveI : (Work.Fitting.pCore ℓ D).Normal := inferInstance
        refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conjNormal d).toEquiv ?_)
        intro x
        have hval : (((MulAut.conjNormal d).toEquiv x : ↥(Work.Fitting.pCore ℓ D)) : D) =
            d * (x : D) * d⁻¹ := MulAut.conjNormal_apply d x
        have hd1 : (ρ d⁻¹) b = a := by
          apply (ρ d).injective
          have h1 : (ρ d) ((ρ d⁻¹) b) = b := by
            rw [← MulAut.mul_apply E (ρ d) (ρ d⁻¹) b, ← map_mul, mul_inv_cancel, map_one]
            rfl
          rw [h1, ← hd]
        change (ρ (x : D)) a = a ↔
          (ρ ((((MulAut.conjNormal d).toEquiv x : ↥(Work.Fitting.pCore ℓ D)) : D))) b = b
        rw [hval]
        have hkey : (ρ (d * (x : D) * d⁻¹)) b = (ρ d) ((ρ (x : D)) a) := by
          rw [map_mul, map_mul]
          simp only [MulAut.mul_apply E]
          rw [hd1]
        rw [hkey]
        constructor
        · intro h; rw [h]; exact hd
        · intro h
          exact (ρ d).injective (h.trans hd.symm)
      have hfaithP : Function.Injective (ρ.comp (Work.Fitting.pCore ℓ D).subtype) :=
        fun x y hxy => Subtype.ext (hfaith (by simpa using hxy))
      have hres := appX_prop hℓprime hℓodd (Work.Fitting.isPGroup_pCore hℓprime) hcop
        (ρ.comp (Work.Fitting.pCore ℓ D).subtype) hfaithP hconst
      exact ⟨hres.1, fun x hx a hxa => hres.2 x hx a (by simpa using hxa)⟩
    have hcycF : IsCyclic ↥(Work.Fitting.fitting D) :=
      appX_cyclic_fitting (fun ℓ hℓ => (key ℓ hℓ).1)
    haveI : Group.IsSolvable D := hFT D hoddD
    refine ⟨hcycF, ?_, ?_⟩
    · refine appX_fpf_fitting ρ ?_
      intro ℓ hℓ x hx hne a ha
      exact (key ℓ hℓ).2 ⟨x, hx⟩ (fun h => hne (congrArg Subtype.val h)) a ha
    · exact appX_commutator_le_fitting hcycF
end Work.ThmF.Tools
