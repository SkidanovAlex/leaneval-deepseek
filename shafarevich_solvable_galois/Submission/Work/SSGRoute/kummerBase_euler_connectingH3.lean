import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The connecting map `H²(G,P) → H³(G,M)` of a short exact sequence, on cocycles

This is the `2 → 3` segment of the long exact sequence whose `0 → … → H²(G,M'')` part lives in
`Work.AbsoluteKummer.SES`.  The construction is the classical one, one degree above
`ShortExactSeq.deltaCocycleC` (`SES/ConnectingH2.lean`): lift a continuous `2`-cocycle `c` with
values in `P` along the surjection `π` to a `2`-cochain `ñ` with values in `N` (composing with a
set-theoretic section, so `ñ` is again continuous), and pull `d²ñ` back along `ι`.  Since `π` is
equivariant and additive and `π ∘ ñ = c`, we have `π (d²ñ) = d²c = 0`, so `d²ñ` takes values in
`ker π = range ι`; and `d³(d²ñ) = 0` by `d3_d2`.

The point of isolating this step is that the *arithmetic* input of the local Euler characteristic
(Milne ADT I.2.8) enters the additivity of `M ↦ [H⁰][H²]/[H¹]` exactly as the hypothesis
`Subsingleton (H3 G M)` ("`H³ = 0`"): with it, `ker δ = ⊤`, so the exactness at `H²(G,P)` gives
that `H²(G,N) → H²(G,P)` is onto, which is what the dimension count needs.
-/

open scoped Classical

universe u v

namespace Work.SSGRoute

open Work.AbsoluteKummer

variable {G : Type u} [TopologicalSpace G] [Group G]

/-! ## `d²` of a `2`-cocycle is zero -/

/-- A `2`-cocycle of the abstract cochain complex has vanishing `d²`. -/
theorem d2_eq_zero_of_mem_Z2 {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    {c : G × G → A} (hc : c ∈ Work.GroupCohomology.Z2 G A) :
    Work.GroupCohomology.d2 G A c = 0 := by
  funext p
  obtain ⟨g, h, k⟩ := p
  rw [Work.GroupCohomology.d2_apply, Pi.zero_apply]
  have h1 : g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h)
      = (g • c (h, k) + c (g, h * k)) - (c (g * h, k) + c (g, h)) := by abel
  rw [h1, hc g h k, sub_self]

/-- `d³` commutes with an equivariant additive map of coefficients. -/
theorem d3_comp {A B : Type*} [AddCommGroup A] [DistribMulAction G A]
    [AddCommGroup B] [DistribMulAction G B] (φ : A →+ B)
    (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a) (x : G × G × G → A) :
    d3 (fun p => φ (x p)) = fun p => φ (d3 x p) := by
  funext p
  obtain ⟨g, h, k, l⟩ := p
  simp only [d3_apply, map_sub, map_add, hφ]

end Work.SSGRoute

namespace Work.AbsoluteKummer.ShortExactSeq

open Work.AbsoluteKummer

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

/-- The lift of a `2`-cochain along `π`, by composing with a set-theoretic section. -/
noncomputable def liftCochain2 (S : ShortExactSeq G M N P) (c : G × G → P) : G × G → N :=
  fun p => S.sect (c p)

@[simp] theorem liftCochain2_apply (S : ShortExactSeq G M N P) (c : G × G → P) (p : G × G) :
    S.liftCochain2 c p = S.sect (c p) := rfl

theorem pi_liftCochain2 (S : ShortExactSeq G M N P) (c : G × G → P) (p : G × G) :
    S.pi (S.liftCochain2 c p) = c p :=
  S.pi_sect (c p)

theorem isLocallyConstant_liftCochain2 (S : ShortExactSeq G M N P) {c : G × G → P}
    (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (S.liftCochain2 c) :=
  Work.AbsoluteKummer.IsLocallyConstant.map S.sect hc

/-- `π` kills `d²` of a lift of a `2`-cocycle: this is what puts the values of the connecting
cocycle in `ker π = range ι`. -/
theorem pi_d2_liftCochain2 (S : ShortExactSeq G M N P) {c : G × G → P}
    (hc : Work.GroupCohomology.d2 G P c = 0) (p : G × G × G) :
    S.pi (Work.GroupCohomology.d2 G N (S.liftCochain2 c) p) = 0 := by
  obtain ⟨g, h, k⟩ := p
  have hc' : Work.GroupCohomology.d2 G P c (g, h, k) = 0 := congrFun hc (g, h, k)
  rw [Work.GroupCohomology.d2_apply] at hc'
  have hg : S.pi (g • S.liftCochain2 c (h, k)) = g • c (h, k) := by
    rw [S.pi_equivariant g, pi_liftCochain2]
  rw [Work.GroupCohomology.d2_apply]
  simp only [map_sub, map_add, hg, pi_liftCochain2]
  exact hc'

/-- **The connecting cocycle** `Z²(G,P) → Z³(G,M)`: lift along `π`, apply `d²`, pull back along
`ι`.  This is the `2 → 3` segment of the long exact sequence. -/
noncomputable def deltaZ3 (S : ShortExactSeq G M N P) (c : Z2 G P) :
    Work.SSGRoute.Z3 (M := M) G :=
  ⟨fun p => S.iotaInv (Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p), by
    refine ⟨?_, ?_⟩
    · -- `d³` of the connecting cocycle vanishes, by injectivity of `ι` and `d³ ∘ d² = 0`
      have hmem : ∀ p : G × G × G,
          Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p ∈ S.iota.range := by
        intro p
        rw [S.range_iota_eq_ker_pi, AddMonoidHom.mem_ker]
        exact pi_d2_liftCochain2 S (Work.SSGRoute.d2_eq_zero_of_mem_Z2 c.2.1) p
      have hfix : (fun p : G × G × G =>
            S.iota (S.iotaInv (Work.GroupCohomology.d2 G N
              (S.liftCochain2 (c : G × G → P)) p)))
          = Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) := by
        funext p
        exact S.iota_iotaInv (hmem p)
      have h1 : Work.SSGRoute.d3 (Work.GroupCohomology.d2 G N
            (S.liftCochain2 (c : G × G → P))) = 0 :=
        Work.SSGRoute.d3_d2 (G := G) (A := N) _
      have h2 : (fun p : G × G × G × G => S.iota (Work.SSGRoute.d3 (fun r => S.iotaInv
            (Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) r)) p))
          = Work.SSGRoute.d3 (fun p : G × G × G => S.iota (S.iotaInv
              (Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) p))) :=
        (Work.SSGRoute.d3_comp S.iota S.iota_equivariant
          (fun r => S.iotaInv (Work.GroupCohomology.d2 G N
            (S.liftCochain2 (c : G × G → P)) r))).symm
      have h3 : (fun p : G × G × G × G => S.iota (Work.SSGRoute.d3 (fun r => S.iotaInv
            (Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) r)) p)) = 0 := by
        rw [h2, hfix]
        exact h1
      funext p
      exact S.iota_injective (by
        have h := congrFun h3 p
        simpa using h)
    · -- local constancy: `ι⁻¹` composed with a locally constant cochain
      exact Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv
        (Work.SSGRoute.isLocallyConstant_d2 S.isDiscreteN
          (isLocallyConstant_liftCochain2 S c.2.2))⟩

end Work.AbsoluteKummer.ShortExactSeq
