import Mathlib
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The mod-`p` Bockstein short exact sequence (AREA EMZ)

Given the Bockstein long exact sequence `BocksteinLES p` (the coefficient sequence
`0 → ℤ --·p--> ℤ → ℤ/p → 0`, its image under `- ⊗ ℤ/p` and the homology long exact
sequence), the first three terms of that long exact sequence assemble into the short
exact sequence

`0 → H_{n+1}(X;ℤ)/p·H_{n+1}(X;ℤ) --f--> H_{n+1}(X;ℤ/p) --g--> H_n(X;ℤ)[p] → 0`

and on finite homology the cardinalities multiply: `|H_{n+1}(X;ℤ/p)|` equals
`|H_{n+1}(X;ℤ)/p·H_{n+1}(X;ℤ)| · |H_n(X;ℤ)[p]|`.

The only non-formal ingredient is Lagrange's theorem in its additive form,
`AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMZ

noncomputable section

/-- **Cardinality of a short exact sequence.**  If `A --f--> B --g--> C` is exact with `f`
injective and `g` surjective, then `Nat.card B = Nat.card A * Nat.card C`.

(Unconditional: `Nat.card` of an infinite type is `0`, and the identity holds in that
degenerate case too, by Lagrange's theorem.) -/
theorem natCard_of_exact {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Nat.card B = Nat.card A * Nat.card C := by
  have hker : f.range = g.ker := (Function.Exact.addMonoidHom_ker_eq hex).symm
  have h1 : Nat.card B = Nat.card (B ⧸ f.range) * Nat.card (f.range : AddSubgroup B) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  have h2 : Nat.card (B ⧸ f.range) = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv
  have h3 : Nat.card (f.range : AddSubgroup B) = Nat.card A :=
    (Nat.card_congr (AddEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hf (by simpa using congrArg Subtype.val h),
        f.rangeRestrict_surjective⟩).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem bocksteinSES (p : ℕ) (hp : p.Prime) (h : Work.Pi6.EMZ.BocksteinLES p) :
    ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
      ∃ (f : (Work.Pi6.HR ℤ X (n + 1) ⧸ Work.Pi6.EMZ.pH p (Work.Pi6.HR ℤ X (n + 1))) →+ Work.Pi6.HR (ZMod p) X (n + 1))
        (g : Work.Pi6.HR (ZMod p) X (n + 1) →+ ↥(Work.Pi6.EMZ.torsP p (Work.Pi6.HR ℤ X n))),
        Function.Injective f ∧ Function.Surjective g ∧ Function.Exact f g ∧
        (Finite (Work.Pi6.HR (ZMod p) X (n + 1)) →
          Nat.card (Work.Pi6.HR (ZMod p) X (n + 1)) =
            Nat.card (Work.Pi6.HR ℤ X (n + 1) ⧸ Work.Pi6.EMZ.pH p (Work.Pi6.HR ℤ X (n + 1))) *
              Nat.card ↥(Work.Pi6.EMZ.torsP p (Work.Pi6.HR ℤ X n))) := by
  obtain ⟨red, del, h1, h2, h3⟩ := h
  intro X _ n
  -- `p · H_{n+1}(X;ℤ) ⊆ ker(red)`, by exactness of the Bockstein sequence at `H_{n+1}(X;ℤ)`
  have hle : pH p (Work.Pi6.HR ℤ X (n + 1)) ≤ (red (X := X) (n + 1)).ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_pH.mp hx
    exact AddMonoidHom.mem_ker.mpr ((h1 X (n + 1) ((p : ℤ) • y)).mpr ⟨y, rfl⟩)
  -- the injection `H_{n+1}(X;ℤ)/p·H_{n+1}(X;ℤ) ↪ H_{n+1}(X;ℤ/p)` induced by `red`
  let f : (Work.Pi6.HR ℤ X (n + 1) ⧸ pH p (Work.Pi6.HR ℤ X (n + 1))) →+
      Work.Pi6.HR (ZMod p) X (n + 1) :=
    QuotientAddGroup.lift (pH p (Work.Pi6.HR ℤ X (n + 1))) (red (X := X) (n + 1)) hle
  -- `del` lands in the `p`-torsion of `H_n(X;ℤ)`, by exactness at `H_n(X;ℤ)`
  have hg_mem : ∀ x : Work.Pi6.HR (ZMod p) X (n + 1),
      del (X := X) n x ∈ torsP p (Work.Pi6.HR ℤ X n) :=
    fun x => mem_torsP.mpr ((h3 X n (del (X := X) n x)).mpr ⟨x, rfl⟩)
  -- the surjection `H_{n+1}(X;ℤ/p) ↠ H_n(X;ℤ)[p]`
  let g : Work.Pi6.HR (ZMod p) X (n + 1) →+ torsP p (Work.Pi6.HR ℤ X n) :=
    (del (X := X) n).codRestrict (torsP p (Work.Pi6.HR ℤ X n)) hg_mem
  have hf_inj : Function.Injective f := by
    rw [← AddMonoidHom.ker_eq_bot_iff]
    rw [AddSubgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hx : red (X := X) (n + 1) x = 0 := by
      simpa [f] using AddMonoidHom.mem_ker.mp hz
    exact (QuotientAddGroup.eq_zero_iff x).mpr (mem_pH.mpr ((h1 X (n + 1) x).mp hx))
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := (h3 X n (y : Work.Pi6.HR ℤ X n)).mp (mem_torsP.mp y.2)
    exact ⟨x, Subtype.ext (by simpa [g] using hx)⟩
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hy' : del (X := X) n y = 0 := by simpa [g] using congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (h2 X n y).mp hy'
      exact ⟨QuotientAddGroup.mk x,
        by rw [show f (QuotientAddGroup.mk x) = red (X := X) (n + 1) x from by simp [f], hx]⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact Subtype.ext
        (by simpa [f, g] using (h2 X n (red (X := X) (n + 1) x)).mpr ⟨x, rfl⟩)
  exact ⟨f, g, hf_inj, hg_surj, hex, fun _ => natCard_of_exact f g hf_inj hg_surj hex⟩

end

end Work.Pi6.EMZ
