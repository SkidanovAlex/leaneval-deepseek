import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.CharCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Classical

/-!
# Area `ThmG2`: Mackey's formula on the two double cosets `H`, `H t H`

The norm computation behind Peterfalvi II, Ch. VI §1 p. 258 (and Ch. V §1–2): in the split
rank-one situation `G = H ∪ H t H` (`t * t = 1`, `t ∉ H`), for any class function `ψ : H → ℂ`,

`‖Ind_H^G ψ‖² = ‖ψ‖² + |D|⁻¹ ∑_{d ∈ D} ψ d · conj (ψ (t d t⁻¹))`, `D = H ⊓ Hᵗ`.

This is the missing `Work.Induction.cfInner_indFun_self_twoDoubleCoset` (there delegated as a
`sorry`); it is proved here self-contained so that area `ThmG2` can discharge the corrected field 6
`Work.ThmG2.IndTwoV2Prop` without waiting for that file.  The mathematics:

* `sum_mul_t_mul_eq` — the fibre/double-coset count: `(a,b) ↦ a t b` counts every element of
  `H t H` exactly `|D|` times (`fiberFun`, `fiberFun_bijective`, `card_fiber`);
* `indFun_apply_mem_eq` — Mackey's restriction formula pointwise on `H`, obtained by splitting the
  defining sum of `Ind_H^G ψ` over `H` and its complement and applying the fibre count;
* `cfInner_indFun_self_twoDoubleCoset` — Frobenius reciprocity plus the pointwise formula, the
  substitution `h ↦ b⁻¹ h b` in the inner sum (`conjMulEquiv`) and the conversion of a `dite` sum
  over `H` into a sum over `D` (`sum_dite_mem_eq_sum_subtype`).
-/

namespace Work.ThmG2

variable {G : Type*} [Group G] [Fintype G]

/-- Membership in `Hᵗ = H.map (MulAut.conj t)`: `x ∈ Hᵗ ↔ t⁻¹ x t ∈ H`. -/
theorem mem_conjMap_iff {H : Subgroup G} {t x : G} :
    x ∈ H.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * x * t ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hh'⟩
    rw [← hh']
    have hconj : (MulAut.conj t).toMonoidHom h = t * h * t⁻¹ := MulAut.conj_apply t h
    rw [hconj]
    have : t⁻¹ * (t * h * t⁻¹) * t = h := by group
    rwa [this]
  · intro hx
    refine ⟨t⁻¹ * x * t, hx, ?_⟩
    have hconj : (MulAut.conj t).toMonoidHom (t⁻¹ * x * t) = t * (t⁻¹ * x * t) * t⁻¹ :=
      MulAut.conj_apply t _
    rw [hconj]
    group

/-- `(t d t)⁻¹ = t d⁻¹ t` when `t * t = 1`. -/
theorem inv_t_mul_t {t d : G} (ht : t * t = 1) : (t * d * t)⁻¹ = t * d⁻¹ * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mul_inv_rev, mul_inv_rev, htinv]
  group

/-- `t * (t * x) = x` when `t * t = 1`. -/
theorem t_mul_t_mul {t x : G} (ht : t * t = 1) : t * (t * x) = x := by
  rw [← mul_assoc, ht, one_mul]

/-- The key cancellation `a d t (t d⁻¹ t) b = a t b` when `t * t = 1`. -/
theorem mul_t_mul_inv_t_mul {t : G} (ht : t * t = 1) (a d b : G) :
    a * d * t * (t * d⁻¹ * t) * b = a * t * b := by
  calc a * d * t * (t * d⁻¹ * t) * b = a * (d * (t * (t * d⁻¹)) * t) * b := by group
    _ = a * (d * d⁻¹ * t) * b := by rw [t_mul_t_mul ht]
    _ = a * t * b := by group

/-- From `a t b = a₀ t b₀` deduce `t (a₀⁻¹ a) t = b₀ b⁻¹`. -/
theorem conj_conj_eq_of_mul_t_mul_eq {t a a₀ b b₀ : G} (ht : t * t = 1)
    (h : a * t * b = a₀ * t * b₀) : t * (a₀⁻¹ * a) * t = b₀ * b⁻¹ := by
  have h1 : a₀⁻¹ * a * t * b = t * b₀ := by
    calc a₀⁻¹ * a * t * b = a₀⁻¹ * (a * t * b) := by group
      _ = a₀⁻¹ * (a₀ * t * b₀) := by rw [h]
      _ = t * b₀ := by group
  have h2 : a₀⁻¹ * a * t = t * b₀ * b⁻¹ := by
    calc a₀⁻¹ * a * t = a₀⁻¹ * a * t * b * b⁻¹ := by group
      _ = t * b₀ * b⁻¹ := by rw [h1]
  calc t * (a₀⁻¹ * a) * t = t * (a₀⁻¹ * a * t) := by group
    _ = t * (t * b₀ * b⁻¹) := by rw [h2]
    _ = (t * t) * b₀ * b⁻¹ := by group
    _ = b₀ * b⁻¹ := by rw [ht, one_mul]

/-- `(t d t⁻¹) ∈ H` for `d ∈ D = H ⊓ Hᵗ`. -/
theorem conj_t_mem_of_mem_inf {H : Subgroup G} {t : G} (ht : t * t = 1) {d : G}
    (hd : d ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom) : (MulAut.conj t) d ∈ H := by
  obtain ⟨h, hh, hh'⟩ := Subgroup.mem_map.mp hd.2
  have hconj : ∀ x : G, (MulAut.conj t) x = t * x * t⁻¹ := fun x => MulAut.conj_apply t x
  have hd_eq : d = t * h * t⁻¹ := by rw [← hh']; exact hconj h
  have htt : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  have hinv : (MulAut.conj t) ((MulAut.conj t) h) = h := by
    rw [hconj, hconj]
    rw [show t * (t * h * t⁻¹) * t⁻¹ = (t * t) * h * (t⁻¹ * t⁻¹) from by group, ht, htt,
      mul_one, one_mul]
  rw [hd_eq, ← hconj h, hinv]
  exact hh

/-- `(t d t)⁻¹ ∈ H` for `d ∈ D = H ⊓ Hᵗ`. -/
theorem inv_conj_t_mem_of_mem_inf {H : Subgroup G} {t : G} (ht : t * t = 1) {d : G}
    (hd : d ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom) : (t * d * t)⁻¹ ∈ H := by
  have hmem : (MulAut.conj t) d ∈ H := conj_t_mem_of_mem_inf ht hd
  have hconj : (MulAut.conj t) d = t * d * t⁻¹ := MulAut.conj_apply t d
  rw [hconj] at hmem
  have h1 : t * d * t = t * d * t⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right ht]
  have heq : (t * d * t)⁻¹ = (t * d * t⁻¹)⁻¹ := by rw [h1]
  rw [heq]
  exact H.inv_mem hmem

/-- The parametrised map `d ↦ (p₀.1 * d, (t d t)⁻¹ * p₀.2)` into the fibre of `(a,b) ↦ a t b`
over `p₀`. -/
noncomputable def fiberFun {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H)
    (d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom)) :
    {p : H × H // (p.1 : G) * t * p.2 = (p₀.1 : G) * t * p₀.2} :=
  ⟨(p₀.1 * ⟨d.1, d.2.1⟩,
      ⟨(t * d.1 * t)⁻¹, inv_conj_t_mem_of_mem_inf ht d.2⟩ * p₀.2), by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_t_mul_t ht]
    rw [show (↑p₀.1 : G) * ↑d * t * (t * (↑d)⁻¹ * t * ↑p₀.2)
        = ((↑p₀.1 : G) * ↑d * t * (t * (↑d)⁻¹ * t)) * ↑p₀.2 from by group]
    exact mul_t_mul_inv_t_mul ht _ _ _⟩

/-- The inverse direction: the `D`-component of a pair in the fibre. -/
noncomputable def fiberInv {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H)
    (p : {p : H × H // (p.1 : G) * t * p.2 = (p₀.1 : G) * t * p₀.2}) :
    ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) :=
  ⟨p₀.1⁻¹ * p.1.1, by
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem p₀.1.2) p.1.1.2, ?_⟩
    rw [mem_conjMap_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_eq_of_mul_eq_one_right ht, conj_conj_eq_of_mul_t_mul_eq ht p.2]
    exact H.mul_mem p₀.2.2 (H.inv_mem p.1.2.2)⟩

theorem fiberFun_injective {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H) :
    Function.Injective (fiberFun ht p₀) := by
  intro d₁ d₂ h
  have h1 : (p₀.1 * ⟨d₁.1, d₁.2.1⟩ : H) = p₀.1 * ⟨d₂.1, d₂.2.1⟩ := by
    have h2 : (fiberFun ht p₀ d₁).1.1 = (fiberFun ht p₀ d₂).1.1 := congrArg (fun q => q.1.1) h
    simpa only [fiberFun] using h2
  have h3 : (⟨d₁.1, d₁.2.1⟩ : H) = ⟨d₂.1, d₂.2.1⟩ := mul_left_cancel h1
  exact Subtype.ext (congrArg (fun x : H => (x : G)) h3)

theorem fiberFun_fiberInv {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H)
    (p : {p : H × H // (p.1 : G) * t * p.2 = (p₀.1 : G) * t * p₀.2}) :
    fiberFun ht p₀ (fiberInv ht p₀ p) = p := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp only [fiberFun, fiberInv, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · apply Subtype.ext
    simp only [fiberFun, fiberInv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_conj_eq_of_mul_t_mul_eq ht hp]
    group

theorem fiberFun_bijective {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H) :
    Function.Bijective (fiberFun ht p₀) :=
  ⟨fiberFun_injective ht p₀, fun p => ⟨fiberInv ht p₀ p, fiberFun_fiberInv ht p₀ p⟩⟩

/-- The number of pairs `(a,b) ∈ H × H` with `a t b = p₀.1 t p₀.2` is `|D|`. -/
theorem card_fiber {H : Subgroup G} {t : G} (ht : t * t = 1) (p₀ : H × H) :
    Nat.card {p : H × H // (p.1 : G) * t * p.2 = (p₀.1 : G) * t * p₀.2}
      = Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact (Fintype.card_of_bijective (fiberFun_bijective ht p₀)).symm

/-- A filtered `Finset.univ` has the cardinality of the corresponding subtype. -/
theorem card_filter_univ_eq_card_subtype {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {a : α // p a} := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype (Finset.univ.filter p) (fun x => by simp)).symm

/-- **The fibre/double-coset count.**  If `G = H ∪ H t H` with `t * t = 1`, `t ∉ H`, then
summing over `H × H` along `(a,b) ↦ a t b` counts every element outside `H` exactly `|D|` times,
`D = H ⊓ Hᵗ`. -/
theorem sum_mul_t_mul_eq {H : Subgroup G} {t : G}
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G)) (f : G → ℂ) :
    (∑ p : H × H, f ((p.1 : G) * t * p.2)) =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) *
        ∑ x : {x : G // x ∉ H}, f x := by
  have hnot : ∀ p : H × H, ((p.1 : G) * t * p.2) ∉ H := by
    intro p hp
    have htmem : t ∈ H := by
      have h1 : (p.1 : G)⁻¹ * ((p.1 : G) * t * p.2) * (p.2 : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem p.1.2) hp) (H.inv_mem p.2.2)
      rwa [show (p.1 : G)⁻¹ * ((p.1 : G) * t * p.2) * (p.2 : G)⁻¹ = t from by group] at h1
    exact htH htmem
  have himage : (Finset.univ.image (fun p : H × H => (p.1 : G) * t * p.2)) =
      Finset.univ.filter (fun x : G => x ∉ H) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨p, rfl⟩
      exact hnot p
    · intro hx
      rcases hcover x with h | ⟨a, b, hx'⟩
      · exact absurd h hx
      · exact ⟨(a, b), hx'.symm⟩
  have hcard : ∀ x ∈ Finset.univ.filter (fun x : G => x ∉ H),
      (Finset.univ.filter (fun p : H × H => (p.1 : G) * t * p.2 = x)).card
        = Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) := by
    intro x hx
    rw [card_filter_univ_eq_card_subtype]
    rcases Finset.mem_filter.mp hx with ⟨-, hxH⟩
    rcases hcover x with h | ⟨a, b, hx'⟩
    · exact absurd h hxH
    · subst hx'
      exact card_fiber ht (a, b)
  rw [Finset.sum_comp f (fun p : H × H => (p.1 : G) * t * p.2), himage,
    Finset.sum_congr rfl (fun x hx => by rw [hcard x hx, nsmul_eq_mul]), ← Finset.mul_sum]
  congr 1
  exact Finset.sum_subtype (Finset.univ.filter (fun x : G => x ∉ H)) (fun x => by simp) f

/-- `(t d t) ∈ H` for `d ∈ D = H ⊓ Hᵗ`. -/
theorem conj_apply_mem_of_mem_inf {H : Subgroup G} {t : G} (ht : t * t = 1) {d : G}
    (hd : d ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom) : t * d * t ∈ H := by
  have hmem : (MulAut.conj t) d ∈ H := conj_t_mem_of_mem_inf ht hd
  have hconj : (MulAut.conj t) d = t * d * t⁻¹ := MulAut.conj_apply t d
  rw [hconj] at hmem
  rwa [show t * d * t = t * d * t⁻¹ from by rw [inv_eq_of_mul_eq_one_right ht]]

/-- Conjugating `t y t` by an element of `H` stays in `H` iff `t y t` does. -/
theorem mem_conj_mul_conj_iff {H : Subgroup G} {t y : G} {a : H} :
    (a : G) * (t * y * t) * (a : G)⁻¹ ∈ H ↔ t * y * t ∈ H := by
  constructor
  · intro hx
    have h1 : (a : G)⁻¹ * ((a : G) * (t * y * t) * (a : G)⁻¹) * (a : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem a.2) hx) a.2
    rwa [show (a : G)⁻¹ * ((a : G) * (t * y * t) * (a : G)⁻¹) * (a : G) = t * y * t from
      by group] at h1
  · intro hx
    exact H.mul_mem (H.mul_mem a.2 hx) (H.inv_mem a.2)

/-- For `y ∈ H`: `t y t ∈ H` iff `y ∈ D = H ⊓ Hᵗ`. -/
theorem conj_t_mem_iff_mem_inf {H : Subgroup G} {t y : G} (ht : t * t = 1) (hy : y ∈ H) :
    t * y * t ∈ H ↔ y ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := by
  constructor
  · intro hx
    refine Subgroup.mem_inf.mpr ⟨hy, ?_⟩
    rw [mem_conjMap_iff, inv_eq_of_mul_eq_one_right ht]
    exact hx
  · intro hyD
    exact conj_apply_mem_of_mem_inf ht hyD

/-- `(a t b) h (a t b)⁻¹ = a (t (b h b⁻¹) t) a⁻¹` when `t * t = 1`. -/
theorem conj_mul_t_mul_eq {t : G} (ht : t * t = 1) (a b h : G) :
    (a * t * b) * h * (a * t * b)⁻¹ = a * (t * (b * h * b⁻¹) * t) * a⁻¹ := by
  rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht]
  group

/-- **Mackey's restriction formula, pointwise.**  For `h ∈ H`,
`Ind_H^G ψ h = ψ h + |D|⁻¹ ∑_{b ∈ H} [b h b⁻¹ ∈ D] ψ (t (b h b⁻¹) t)`, `D = H ⊓ Hᵗ`. -/
theorem indFun_apply_mem_eq {H : Subgroup G} {t : G}
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G))
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) (h : H) :
    Work.Induction.indFun H ψ (h : G) = ψ h +
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
        ∑ b : H, (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
            (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
          then ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t, conj_apply_mem_of_mem_inf ht hb⟩
          else 0) := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcardD : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, by
      refine Subgroup.mem_inf.mpr ⟨H.one_mem, ?_⟩
      rw [mem_conjMap_iff]
      simp⟩, inferInstance⟩
  let Gb : G → ℂ := fun x =>
    if hx : x * (h : G) * x⁻¹ ∈ H then ψ ⟨x * (h : G) * x⁻¹, hx⟩ else 0
  let Sb : H → ℂ := fun b =>
    if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t, conj_apply_mem_of_mem_inf ht hb⟩ else 0
  have hsplit : (∑ x : G, Gb x) = (∑ x : {x : G // x ∈ H}, Gb x) +
      ∑ x : {x : G // x ∉ H}, Gb x :=
    (Fintype.sum_subtype_add_sum_subtype (fun x : G => x ∈ H) Gb).symm
  have h1 : (∑ x : {x : G // x ∈ H}, Gb x) = (Nat.card ↥H : ℂ) * ψ h := by
    rw [Finset.sum_congr rfl (fun x _ => ?_), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
    dsimp only [Gb]
    have hxH : (x:G) * (h:G) * (x:G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem x.2 h.2) (H.inv_mem x.2)
    rw [dite_eq_left hxH]
    rw [show (⟨(x:G) * (h:G) * (x:G)⁻¹, hxH⟩ : H) = x * h * x⁻¹ from
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])]
    exact hψ h x
  have hpair : (∑ p : H × H, Gb ((p.1 : G) * t * p.2)) = (Nat.card ↥H : ℂ) * ∑ b : H, Sb b := by
    have hterm : ∀ p : H × H, Gb ((p.1 : G) * t * p.2) = Sb p.2 := by
      intro p
      obtain ⟨a, b⟩ := p
      dsimp only [Gb, Sb]
      by_cases hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
          (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      · have hX : t * ((b:G) * (h:G) * (b:G)⁻¹) * t ∈ H := conj_apply_mem_of_mem_inf ht hb
        have hcond : ((a:G) * t * b) * (h:G) * ((a:G) * t * b)⁻¹ ∈ H := by
          rw [conj_mul_t_mul_eq ht (a:G) (b:G) (h:G)]
          exact (mem_conj_mul_conj_iff (H := H) (t := t)
            (y := (b:G) * (h:G) * (b:G)⁻¹) (a := a)).mpr hX
        rw [dite_eq_left hcond, dite_eq_left hb]
        rw [← hψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t, conj_apply_mem_of_mem_inf ht hb⟩ a]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact conj_mul_t_mul_eq ht (a:G) (b:G) (h:G)
      · have hcond : ¬ (((a:G) * t * b) * (h:G) * ((a:G) * t * b)⁻¹ ∈ H) := by
          intro hc
          have h2 : (a:G) * (t * ((b:G) * (h:G) * (b:G)⁻¹) * t) * (a:G)⁻¹ ∈ H := by
            rw [← conj_mul_t_mul_eq ht (a:G) (b:G) (h:G)]
            exact hc
          exact hb ((conj_t_mem_iff_mem_inf ht
            (H.mul_mem (H.mul_mem b.2 h.2) (H.inv_mem b.2))).mp
            ((mem_conj_mul_conj_iff (H := H) (t := t)
              (y := (b:G) * (h:G) * (b:G)⁻¹) (a := a)).mp h2))
        rw [dite_eq_right hcond, dite_eq_right hb]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), Fintype.sum_prod_type]
    rw [show (∑ x : H, ∑ y : H, Sb (x, y).2) = ∑ x : H, ∑ y : H, Sb y from
      Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => rfl))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have h2 : (∑ x : {x : G // x ∉ H}, Gb x) =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
        ((Nat.card ↥H : ℂ) * ∑ b : H, Sb b) := by
    have hA := sum_mul_t_mul_eq (H := H) (t := t) ht htH hcover Gb
    rw [hpair] at hA
    calc (∑ x : {x : G // x ∉ H}, Gb x)
        = (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
            ((Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) *
              ∑ x : {x : G // x ∉ H}, Gb x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hcardD, one_mul]
      _ = (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
            ((Nat.card ↥H : ℂ) * ∑ b : H, Sb b) := by rw [hA]
  have hdef : (Nat.card ↥H : ℂ) * Work.Induction.indFun H ψ (h : G) = ∑ x : G, Gb x := by
    rw [Work.Induction.indFun_apply_def, ← mul_assoc, mul_inv_cancel₀ hcardH, one_mul]
  refine mul_left_cancel₀ hcardH ?_
  rw [hdef, hsplit, h1, h2]
  dsimp only [Sb]
  ring

/-- The subtype `{h : H // h ∈ D}` is `D` itself. -/
noncomputable def subtypeDEquiv {H D : Subgroup G} (hDH : D ≤ H) :
    {h : H // (h:G) ∈ (D : Set G)} ≃ ↥D where
  toFun h := ⟨h.1.1, h.2⟩
  invFun d := ⟨⟨d.1, hDH d.2⟩, d.2⟩
  left_inv h := Subtype.ext (Subtype.ext rfl)
  right_inv d := Subtype.ext rfl

/-- A `dite` sum over `H` restricted to the subgroup `D ≤ H` is the sum over `D`. -/
theorem sum_dite_mem_eq_sum_subtype {H D : Subgroup G} (hDH : D ≤ H) (f : ↥D → ℂ) :
    (∑ h : H, (if hh : (h:G) ∈ (D : Set G) then f ⟨h.1, hh⟩ else 0)) = ∑ d : ↥D, f d := by
  have h1 : (∑ h : H, (if hh : (h:G) ∈ (D : Set G) then f ⟨h.1, hh⟩ else 0)) =
      ∑ a : {h : H // (h:G) ∈ (D : Set G)}, f ⟨a.1.1, a.2⟩ := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (p := fun h : H => (h:G) ∈ (D : Set G))
      (f := fun h => if hh : (h:G) ∈ (D : Set G) then f ⟨h.1, hh⟩ else 0)
    rw [← hsplit]
    rw [show (∑ a : {h : H // ¬ ((h:G) ∈ (D : Set G))},
          (if hh : (a:G) ∈ (D : Set G) then f ⟨a.1, hh⟩ else 0)) = 0 from
      Finset.sum_eq_zero (fun a _ => dite_eq_right (by simpa using a.2)), add_zero]
    exact Finset.sum_congr rfl (fun a _ => dite_eq_left a.2)
  rw [h1]
  exact Equiv.sum_comp (subtypeDEquiv hDH) f

/-- Conjugation by `b` as a permutation of `H`. -/
noncomputable def conjMulEquiv {H : Subgroup G} (b : H) : H ≃ H where
  toFun h := b * h * b⁻¹
  invFun h := b⁻¹ * h * b
  left_inv h := by group
  right_inv h := by group

/-- **Mackey's formula on the two double cosets `H`, `H t H`.**  In the split rank-one situation
`G = H ∪ H t H`, `t * t = 1`, `t ∉ H`, for any class function `ψ : H → ℂ`,
`‖Ind_H^G ψ‖² = ‖ψ‖² + |D|⁻¹ ∑_{d ∈ D} ψ d · conj (ψ (t d t⁻¹))`, `D = H ⊓ Hᵗ`. -/
theorem cfInner_indFun_self_twoDoubleCoset {G : Type*} [Group G] [Fintype G]
    {H : Subgroup G} {t : G}
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G))
    (hDmap : ∀ d : (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        (MulAut.conj t) (d:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H ψ) (Work.Induction.indFun H ψ)
      = Work.CharCore.cfInner ψ ψ + (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
            ψ ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hDmem : (1 : G) ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨H.one_mem, ?_⟩
    rw [mem_conjMap_iff]
    simp
  have hcardD : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, hDmem⟩, inferInstance⟩
  -- the second term of the pointwise Mackey restriction formula
  let SS : H → ℂ := fun h => ∑ b : H,
    (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t, conj_apply_mem_of_mem_inf ht hb⟩ else 0)
  let FF : H → ℂ := fun h =>
    (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * SS h
  let T : H → H → ℂ := fun b h => ψ h *
    (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then (starRingEnd ℂ) (ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t,
        conj_apply_mem_of_mem_inf ht hb⟩) else 0)
  let T' : H → ℂ := fun h => ψ h *
    (if hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then (starRingEnd ℂ) (ψ ⟨t * (h:G) * t, conj_apply_mem_of_mem_inf ht hh⟩) else 0)
  -- Frobenius reciprocity
  rw [Work.Induction.frobenius_reciprocity (H := H) ψ (Work.Induction.indFun H ψ)
    (Work.Induction.isClassFun_indFun H ψ)]
  -- the pointwise restriction formula of Mackey
  have hres : Work.Induction.resFun H (Work.Induction.indFun H ψ) = ψ + FF := by
    funext h
    have hpt := indFun_apply_mem_eq (H := H) (t := t) ht htH hcover ψ hψ h
    simpa only [Work.Induction.resFun_apply, Pi.add_apply, FF, SS] using hpt
  rw [hres, Work.CharCore.cfInner_add_right]
  congr 1
  -- the norm computation
  have hstarFF : ∀ h : H, (starRingEnd ℂ) (FF h) =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * (starRingEnd ℂ) (SS h) := by
    intro h
    dsimp only [FF]
    rw [map_mul]
    congr 1
    simp
  have hstarSS : ∀ h : H, (starRingEnd ℂ) (SS h) = ∑ b : H,
      (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
        then (starRingEnd ℂ) (ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t,
          conj_apply_mem_of_mem_inf ht hb⟩) else 0) := by
    intro h
    dsimp only [SS]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
        (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
    · rw [dite_eq_left hb, dite_eq_left hb]
    · rw [dite_eq_right hb, dite_eq_right hb]
      simp
  -- step 1: expand the star of the sum
  have hstep1 : (∑ h : H, ψ h * (starRingEnd ℂ) (SS h)) = ∑ b : H, ∑ h : H, T b h := by
    have h1 : ∀ h : H, ψ h * (starRingEnd ℂ) (SS h) = ∑ b : H, T b h := by
      intro h
      rw [hstarSS h, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_comm]
  -- step 2: the substitution `h ↦ b⁻¹ h b` in the inner sum
  have hstep2 : ∀ b : H, (∑ h : H, T b h) = ∑ h : H, T' h := by
    intro b
    have hterm : ∀ h : H, T b h = T' (b * h * b⁻¹) := by
      intro h
      dsimp only [T, T']
      have hcond : (((b * h * b⁻¹ : H)) : G) = (b:G) * (h:G) * (b:G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      by_cases hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
          (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      · have hb' : ((((b * h * b⁻¹ : H)) : G)) ∈
            (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G) := by
          rw [hcond]; exact hb
        rw [dite_eq_left hb, dite_eq_left hb', hψ h b]
        exact congrArg (fun z : H => ψ h * (starRingEnd ℂ) (ψ z)) (Subtype.ext rfl)
      · have hb' : ¬ ((((b * h * b⁻¹ : H)) : G)) ∈
            (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G) := by
          rw [hcond]; exact hb
        rw [dite_eq_right hb, dite_eq_right hb']
        simp
    rw [Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_congr rfl (fun h _ =>
        (show T' (b * h * b⁻¹) = T' ((conjMulEquiv b) h) from rfl)),
      Equiv.sum_comp (conjMulEquiv b) T']
  -- step 3: convert to a sum over `D`
  have hstep3 : (∑ h : H, T' h) =
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        ψ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩) := by
    have h1 : (∑ h : H, T' h) = ∑ h : H,
        (if hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
          then ψ h * (starRingEnd ℂ) (ψ ⟨t * (h:G) * t,
            conj_apply_mem_of_mem_inf ht hh⟩) else 0) :=
      Finset.sum_congr rfl (fun h _ => by
        dsimp only [T']
        by_cases hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
        · rw [dite_eq_left hh, dite_eq_left hh]
        · rw [dite_eq_right hh, dite_eq_right hh]
          simp)
    rw [h1]
    exact sum_dite_mem_eq_sum_subtype (H := H)
      (D := H ⊓ H.map (MulAut.conj t).toMonoidHom) inf_le_left
      (fun d => ψ ⟨(d:G), d.2.1⟩ *
        (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩))
  have hself : (∑ h : H, ψ h * (starRingEnd ℂ) (SS h)) = (Nat.card ↥H : ℂ) *
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        ψ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩) := by
    rw [hstep1, Finset.sum_congr rfl (fun b _ => hstep2 b), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card, hstep3]
  have hmain : Work.CharCore.cfInner ψ FF =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * (Fintype.card ↥H : ℂ)⁻¹ *
        (∑ h : H, ψ h * (starRingEnd ℂ) (SS h)) := by
    rw [Work.CharCore.cfInner]
    rw [Finset.sum_congr rfl (fun h _ => by rw [hstarFF h])]
    rw [show (∑ h : H, ψ h * ((Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          (starRingEnd ℂ) (SS h))) =
        (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          ∑ h : H, ψ h * (starRingEnd ℂ) (SS h) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h _ => by ring)]
    ring
  -- rewrite the conjugating element `t · t` as `MulAut.conj t`
  have hDsum : (∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        ψ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩)) =
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        ψ ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (ψ ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have h1 : (⟨(d:G), d.2.1⟩ : H) = ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ :=
      Subtype.ext rfl
    have h2 : (⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩ : H) =
        ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩ := by
      apply Subtype.ext
      show t * (d:G) * t = (MulAut.conj t) (d:G)
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht]
    rw [show (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩) =
        star (ψ ⟨t * (d:G) * t, conj_apply_mem_of_mem_inf ht d.2⟩) from rfl, h1, h2]
  rw [hmain, hself, ← Nat.card_eq_fintype_card, hDsum]
  field_simp

end Work.ThmG2
