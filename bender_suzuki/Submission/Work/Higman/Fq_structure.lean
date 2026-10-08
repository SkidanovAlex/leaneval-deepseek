import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-!
# Step 4: the `𝔽_q`-structure of the layers `A / A²`, `A² / A⁴`, …

Higman 1963, §3–§4.  For a `ξ`-invariant abelian normal subgroup `A` of a Suzuki 2-group,
`A` is homocyclic of exponent `2 ^ e` (`homogeneous_structure`), the `2 ^ (e-1)`-st power map is a
`ξ`-equivariant bijection `A / A² ≅ A ⊓ Ω₁ = Ω₁` (`mem_powSub_two_iff`), and `ξ` acts transitively
on the involutions, hence on the non-identity elements of `Ω₁` and therefore on the non-identity
elements of `A / A²`.  Everything in steps 4–5 (the identification of `C/A`, `A/A²`, `A²/A⁴` with
`𝔽_q`, the normal form of a `ξ`-equivariant biadditive map, and the monomial expansion of the
bracket) rests on that.

The statements below are deliberately *elementwise* (`ξ ^ k a · b⁻¹ ∈ A ^ (2)`) so that the
quotient `A / A²` is not needed to state them.
-/

/-- The `2 ^ (e-1)`-st power of a non-`A²`-element of the homocyclic group `A` is a
non-identity involution.  `2 ^ e` is the exponent of `A`. -/
theorem pow_two_pow_sub_one_mem_omega1 (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1)
    (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) (he : 1 ≤ e) {a : P}
    (ha : a ∈ A) (ha2 : a ∉ powSub A 2) :
    a ^ 2 ^ (e - 1) ∈ omega1 P ∧ a ^ 2 ^ (e - 1) ≠ 1 := by
  have hk2 : 2 ^ (e - 1) * 2 = 2 ^ e := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · rw [h.mem_omega1, ← pow_mul, hk2]
    exact he1 a ha
  · intro h1
    exact ha2 ((hkey a ha).mpr h1)

/-- **Step 4, first lemma.**  `ξ` acts transitively on the non-identity elements of `A / A ^ (2)`:
for `a, b ∈ A` with `a, b ∉ A ^ (2)` there is `k` with `ξ ^ k a ≡ b (mod A ^ (2))`. -/
theorem exists_xi_pow_mul_inv_mem_powSub_two (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) {a b : P} (ha : a ∈ A) (hb : b ∈ A)
    (ha2 : a ∉ powSub A 2) (hb2 : b ∉ powSub A 2) :
    ∃ k : ℕ, (h.xi ^ k) a * b⁻¹ ∈ powSub A 2 := by
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      have hbot : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hx1 := he1 x hx
        rw [h0] at hx1
        simpa using hx1
      have hmem : a ∈ powSub A 2 := by
        have hbot' : powSub A 2 = ⊥ := by
          rw [hbot]
          exact le_antisymm (powSub_le (by norm_num)) bot_le
        rw [hbot']
        exact hbot ▸ ha
      exact ha2 hmem
    · exact hpos
  obtain ⟨hak_mem, hak_ne⟩ := pow_two_pow_sub_one_mem_omega1 h hA he1 hkey he ha ha2
  obtain ⟨hbk_mem, hbk_ne⟩ := pow_two_pow_sub_one_mem_omega1 h hA he1 hkey he hb hb2
  -- these are involutions, so `ξ` relates them
  have hako : orderOf (a ^ 2 ^ (e - 1)) = 2 := by
    have h2 := h.mem_omega1.mp hak_mem
    have hd : orderOf (a ^ 2 ^ (e - 1)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
    · exact absurd (orderOf_eq_one_iff.mp h1) hak_ne
    · exact h2'
  have hbko : orderOf (b ^ 2 ^ (e - 1)) = 2 := by
    have h2 := h.mem_omega1.mp hbk_mem
    have hd : orderOf (b ^ 2 ^ (e - 1)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
    · exact absurd (orderOf_eq_one_iff.mp h1) hbk_ne
    · exact h2'
  obtain ⟨m, hm⟩ := h.trans (a ^ 2 ^ (e - 1)) (b ^ 2 ^ (e - 1)) hako hbko
  refine ⟨m, ?_⟩
  -- `ξ ^ m a ∈ A`
  have hpres : ∀ j : ℕ, ∀ y : P, y ∈ A → (h.xi ^ j) y ∈ A := by
    intro j
    induction j with
    | zero => intro y hy; simpa using hy
    | succ j ih =>
        intro y hy
        have hz : (h.xi ^ j) y ∈ A := ih y hy
        have hgoal : (h.xi ^ (j + 1)) y = h.xi.toMonoidHom ((h.xi ^ j) y) := by
          rw [pow_succ', MulAut.mul_apply]; rfl
        rw [hgoal]
        have hmem : h.xi.toMonoidHom ((h.xi ^ j) y) ∈ A.map (h.xi : MulAut P).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hz
        rwa [hA.map_eq] at hmem
  have hmemA : (h.xi ^ m) a * b⁻¹ ∈ A :=
    A.mul_mem (hpres m a ha) (A.inv_mem hb)
  refine (hkey _ hmemA).mpr ?_
  have hcomm : Commute ((h.xi ^ m) a) b⁻¹ :=
    hA.abelian _ (hpres m a ha) _ (A.inv_mem hb)
  have hpow : ((h.xi ^ m) a * b⁻¹) ^ 2 ^ (e - 1) = ((h.xi ^ m) a) ^ 2 ^ (e - 1) * (b⁻¹) ^ 2 ^ (e - 1)
      := hcomm.mul_pow _
  rw [hpow, ← map_pow, hm, inv_pow, mul_inv_cancel]


/-! ## The coordinate identification `A / A² ≅ Ω₁`

The `2 ^ (e-1)`-st power map `a ↦ a ^ 2 ^ (e-1)` (where `2 ^ e` is the exponent of the homocyclic
group `A`) descends to `A / A²` and lands in `Ω₁`; it is injective and onto `A ⊓ Ω₁`.  Concretely:
it is **constant on the `A²`-cosets** (so it is a well-defined map `A/A² → Ω₁`) and
**injective modulo `A²`** (so it is a bijection).  These are the coordinates in which the
monomial expansion of the bracket `⌊·,·⌋ : C/A × A/A² → A²/A⁴` is written.
-/

/-- **Coordinate identification, well-definedness.**  The power map `a ↦ a ^ 2 ^ (e-1)` is constant
on the `A²`-cosets of `A`, hence descends to `A / A²`. -/
theorem pow_two_pow_sub_one_class (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) {a b : P} (ha : a ∈ A) (hb : b ∈ A)
    (hab : b * a⁻¹ ∈ powSub A 2) : b ^ 2 ^ (e - 1) = a ^ 2 ^ (e - 1) := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    have hA0 : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have := he1 x hx
      simpa using this
    rw [hA0] at ha hb
    rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]
  · obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hab
    have hb' : b = (d * d) * a := by
      rw [← pow_two, hd]
      group
    have hcomm : Commute (d * d) a :=
      (hA.abelian a ha (d * d) (A.mul_mem hdA hdA)).symm
    have hpow : ((d * d) * a) ^ 2 ^ (e - 1)
        = (d * d) ^ 2 ^ (e - 1) * a ^ 2 ^ (e - 1) := hcomm.mul_pow _
    have hd2 : (d * d) ^ 2 ^ (e - 1) = 1 := by
      have hk : 2 * 2 ^ (e - 1) = 2 ^ e := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel he]
      have hdsq : (d * d) ^ 2 ^ (e - 1) = d ^ (2 * 2 ^ (e - 1)) := by
        rw [← pow_two, ← pow_mul]
      rw [hdsq, hk]
      exact he1 d hdA
    rw [hb', hpow, hd2, one_mul]

/-- **Coordinate identification, injectivity.**  The power map `a ↦ a ^ 2 ^ (e-1)` is injective
modulo `A²`: it separates `A²`-cosets. -/
theorem pow_two_pow_sub_one_inj (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) {a b : P} (ha : a ∈ A)
    (hb : b ∈ A) (hab : b ^ 2 ^ (e - 1) = a ^ 2 ^ (e - 1)) : b * a⁻¹ ∈ powSub A 2 := by
  refine (hkey _ (A.mul_mem hb (A.inv_mem ha))).mpr ?_
  have hcomm : Commute b a⁻¹ :=
    (hA.abelian a⁻¹ (A.inv_mem ha) b hb).symm
  rw [hcomm.mul_pow, inv_pow, hab, mul_inv_cancel]


/-! ## The layer-up coordinates `A² / A⁴ ≅ Ω₁`

The same power map, applied one layer up, gives `A² / A⁴ ≅ A ⊓ Ω₁`: the group `A ^ (2)` is again
homocyclic, of exponent `2 ^ (e-1)`, and its square subgroup is `A ^ (4)`.  So the layer-up
statement reduces to the first-layer one applied to `powSub A 2` — this is what makes the bracket
`⌊·,·⌋ : C/A × A/A² → A²/A⁴` a biadditive map between two copies of the *same* module.
-/

/-- The layer `A ^ (2)` has exponent `2 ^ (e-1)`. -/
theorem powSub_two_exp (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) {x : P} (hx : x ∈ powSub A 2) : x ^ 2 ^ (e - 1) = 1 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    have hA0 : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      have := he1 y hy
      simpa using this
    have hbot : powSub A 2 = ⊥ := by
      rw [hA0]
      exact le_antisymm (powSub_le (by norm_num)) bot_le
    rw [hbot] at hx
    rw [Subgroup.mem_bot.mp hx]
    simp
  · obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hx
    rw [← hd]
    have hk : 2 * 2 ^ (e - 1) = 2 ^ e := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel he]
    rw [← pow_mul, hk]
    exact he1 d hdA

/-- `A ^ (2)` is again a `ξ`-invariant abelian normal subgroup. -/
theorem isXiAbelNormal_powSub_two (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) : IsXiAbelNormal h (powSub A 2) := by
  refine ⟨Subgroup.Normal.mk ?_, map_powSub (h.xi : MulAut P) hA.map_eq 2, ?_⟩
  · intro x hx g
    obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hx
    rw [← hd, pow_two, show g * (d * d) * g⁻¹ = (g * d * g⁻¹) * (g * d * g⁻¹) from by group,
      ← pow_two]
    exact pow_mem_powSub (hA.normal.conj_mem d hdA g)
  · intro x hx y hy
    exact hA.abelian x (powSub_le (by norm_num) hx) y (powSub_le (by norm_num) hy)

/-- **Layer-up coordinates, well-definedness.**  The power map `a ↦ a ^ 2 ^ (e-2)` on `A²` is
constant on the `A⁴`-cosets: it descends to `A² / A⁴ → Ω₁`.  (Proof: apply
`pow_two_pow_sub_one_class` to the subgroup `powSub A 2`, whose exponent is `2 ^ (e-1)` and whose
square subgroup is `A ^ (4)`.) -/
theorem pow_two_pow_sub_two_class (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) {x y : P} (hx : x ∈ powSub A 2)
    (hy : y ∈ powSub A 2) (hab : y * x⁻¹ ∈ powSub A 4) :
    y ^ 2 ^ (e - 2) = x ^ 2 ^ (e - 2) := by
  have hB : IsXiAbelNormal h (powSub A 2) := isXiAbelNormal_powSub_two h hA
  have he1' : ∀ z ∈ powSub A 2, z ^ 2 ^ (e - 1) = 1 := fun z hz => powSub_two_exp h hA he1 hz
  have h2 : y * x⁻¹ ∈ powSub (powSub A 2) 2 := by
    rw [powSub_powSub hA.abelian, show (2:ℕ) * 2 = 4 from by norm_num]
    exact hab
  have hmain := pow_two_pow_sub_one_class h hB he1' hx hy h2
  rwa [show e - 1 - 1 = e - 2 from by omega] at hmain


/-- **Layer-2 kernel statement.**  For `x ∈ A ^ (2)` one has `x ∈ A ^ (4) ↔ x ^ 2 ^ (e-2) = 1`.
This is the kernel of the power map on the second layer: `x = d²` and then
`x ∈ A⁴ ⟺ d ∈ A² ⟺ d ^ 2^(e-1) = 1 ⟺ x ^ 2^(e-2) = 1` (the middle step is the first-layer
kernel statement, the outer steps are the same power bookkeeping).  Together with
`pow_two_pow_sub_two_class` this gives the bijection `A²/A⁴ ≅ Ω₁`. -/
theorem powSub_four_ker (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1)
    (hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) {x : P} (hx : x ∈ powSub A 2) :
    x ∈ powSub A 4 ↔ x ^ 2 ^ (e - 2) = 1 := by
  rcases Nat.lt_or_ge e 2 with he | he
  · -- `e ≤ 1`: then `A ^ (2) = ⊥`, so `x = 1` and both sides are trivial
    have hbot : powSub A 2 = ⊥ :=
      powSub_eq_bot_of_exp (A := A) hA.abelian (k := 1) (by omega) he1
    rw [hbot] at hx
    have hx1 : x = 1 := by simpa using Subgroup.mem_bot.mp hx
    subst hx1
    have hz : (2 : ℕ) ^ (e - 2) = 1 := by
      rw [show e - 2 = 0 from by omega, pow_zero]
    rw [hz, pow_one]
    exact ⟨fun _ => rfl, fun _ => (powSub A 4).one_mem⟩
  · obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hx
    constructor
    · -- `x ∈ A⁴` gives `x = c ^ 4`, so `x ^ 2 ^ (e-2) = c ^ 2 ^ e = 1`
      intro hx4
      obtain ⟨c, hcA, hc⟩ := (mem_powSub_iff hA.abelian).mp hx4
      have hk : 2 ^ 2 * 2 ^ (e - 2) = 2 ^ e := by
        rw [← pow_add]; congr 1; omega
      rw [← hc, show (4:ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, hk]
      exact he1 c hcA
    · -- `x ^ 2 ^ (e-2) = 1` gives `d ^ 2 ^ (e-1) = 1`, so `d ∈ A²` and `x = d² ∈ A⁴`
      intro hxz
      have h2 : 2 * 2 ^ (e - 2) = 2 ^ (e - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hd1 : d ^ 2 ^ (e - 1) = 1 := by
        have hstep : (d ^ 2) ^ 2 ^ (e - 2) = d ^ 2 ^ (e - 1) := by
          rw [← pow_mul, h2]
        rw [← hd] at hxz
        rwa [hstep] at hxz
      have hdA2 : d ∈ powSub A 2 := (hkey d hdA).mpr hd1
      obtain ⟨c, hcA, hc⟩ := (mem_powSub_iff hA.abelian).mp hdA2
      have hx4 : x = c ^ 4 := by
        rw [← hd, ← hc, ← pow_mul, show (2 : ℕ) * 2 = 4 from by norm_num]
      rw [hx4]
      exact pow_mem_powSub (A := A) (n := 4) hcA

end Work.Higman
