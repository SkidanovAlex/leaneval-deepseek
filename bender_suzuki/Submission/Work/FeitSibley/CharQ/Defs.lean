import Submission.Work.FeitSibley.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: the direct-product structure `Q = S × Q₁` and the tensor of characters

Since `S ⊓ Q₁ = ⊥`, `S ⊔ Q₁ = Q` and `S`, `Q₁` commute elementwise, the map
`S × Q₁ → Q`, `(a,b) ↦ a * b` is an isomorphism of groups (`prodIso`).  Transporting the
product of a character `lam` of `S` and a character `theta` of `Q₁` along it gives the character
`prodChar h lam theta` of `Q`; `Irr Q ↔ Irr S × Irr Q₁` under this correspondence.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FeitSibley

variable {G : Type} [Group G] [Fintype G]

namespace FSData

variable (h : FSData G)

/-- The canonical homomorphism `S × Q₁ → Q`, `(a,b) ↦ a * b`. -/
noncomputable def prodHom : ↥h.S × ↥h.Q1 →* ↥h.Q where
  toFun x := ⟨(x.1 : G) * (x.2 : G), h.mem_Q_iff.mpr ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show ((x.1 * y.1 : ↥h.S) : G) * ((x.2 * y.2 : ↥h.Q1) : G)
      = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
    simp only [Subgroup.coe_mul]
    have hc : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) :=
      h.commute (y.1 : G) y.1.2 (x.2 : G) x.2.2
    calc (x.1 : G) * (y.1 : G) * ((x.2 : G) * (y.2 : G))
        = (x.1 : G) * ((y.1 : G) * ((x.2 : G) * (y.2 : G))) := by rw [mul_assoc]
      _ = (x.1 : G) * (((y.1 : G) * (x.2 : G)) * (y.2 : G)) := by rw [mul_assoc]
      _ = (x.1 : G) * (((x.2 : G) * (y.1 : G)) * (y.2 : G)) := by rw [hc]
      _ = (x.1 : G) * ((x.2 : G) * ((y.1 : G) * (y.2 : G))) := by rw [mul_assoc]
      _ = (x.1 : G) * (x.2 : G) * ((y.1 : G) * (y.2 : G)) := by rw [mul_assoc]

@[simp] theorem prodHom_apply (x : ↥h.S × ↥h.Q1) :
    ((h.prodHom x : ↥h.Q) : G) = (x.1 : G) * (x.2 : G) := rfl

theorem prodHom_bijective : Function.Bijective h.prodHom := by
  constructor
  · intro x y hxy
    have h1 : ((x.1 : G) * (x.2 : G)) = ((y.1 : G) * (y.2 : G)) :=
      congrArg (fun z : ↥h.Q => (z : G)) hxy
    obtain ⟨ha, hb⟩ := h.mul_eq_of_Q_decomp x.1.2 y.1.2 x.2.2 y.2.2 h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  · intro q
    obtain ⟨a, ha, b, hb, hab⟩ := h.mem_Q_decomp q.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab.symm⟩

/-- `Q ≅ S × Q₁`, realised by `(a, b) ↦ a * b`. -/
noncomputable def prodIso : ↥h.S × ↥h.Q1 ≃* ↥h.Q :=
  MulEquiv.ofBijective h.prodHom h.prodHom_bijective

@[simp] theorem prodIso_apply (x : ↥h.S × ↥h.Q1) : h.prodIso x = h.prodHom x := rfl

theorem prodIso_symm_mul (q : ↥h.Q) :
    ((h.prodIso.symm q).1 : G) * ((h.prodIso.symm q).2 : G) = (q : G) := by
  have h2 := h.prodIso.apply_symm_apply q
  have h3 : ((h.prodIso (h.prodIso.symm q) : ↥h.Q) : G) = (q : G) := congrArg Subtype.val h2
  simpa only [prodIso_apply, prodHom_apply] using h3

/-- The character of `Q` obtained from a function on `S` and a function on `Q₁`
(`prodChar h lam theta q = lam a * theta b` where `q = a * b`). -/
noncomputable def prodChar (lam : ↥h.S → ℂ) (theta : ↥h.Q1 → ℂ) : ↥h.Q → ℂ :=
  fun q => lam ((h.prodIso.symm q).1) * theta ((h.prodIso.symm q).2)

theorem prodChar_apply (lam : ↥h.S → ℂ) (theta : ↥h.Q1 → ℂ) (a : ↥h.S) (b : ↥h.Q1) :
    h.prodChar lam theta (h.prodIso (a, b)) = lam a * theta b := by
  simp only [prodChar, MulEquiv.symm_apply_apply]

theorem prodChar_one (lam : ↥h.S → ℂ) (theta : ↥h.Q1 → ℂ) :
    h.prodChar lam theta 1 = lam 1 * theta 1 := by
  have h1 : h.prodIso.symm (1 : ↥h.Q) = 1 := map_one _
  simp only [prodChar, h1, Prod.fst_one, Prod.snd_one]

/-- `Ind_Q^H φ`, as a function on `H`, for `φ` a function on `Q`. -/
noncomputable def indQH (phi : ↥h.Q → ℂ) : ↥h.H → ℂ :=
  Work.Induction.indFun (h.Q.subgroupOf h.H)
    (fun x : ↥(h.Q.subgroupOf h.H) => phi ⟨(x : G), x.2⟩)

end FSData

end Work.FeitSibley
