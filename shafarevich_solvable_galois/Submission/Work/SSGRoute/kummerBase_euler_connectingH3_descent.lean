import Mathlib
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.SES.Connecting
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The descent: `deltaZ3` is well defined on `H²(G,P)`

`Work.SSGRoute.kummerBase_euler_connectingH3` constructs the connecting *cocycle*
`deltaZ3 : Z²(G,P) → Z³(G,M)` of a short exact sequence `0 → M → N → P → 0` of discrete
`G`-modules.  This file descends it to the cohomology: the class of `deltaZ3 c` depends only on
the class of `c` in `H²(G,P)`, so that

  `deltaH3 : H²(G,P) →+ H³(G,M)`

is defined.  The two ingredients are the classical ones:

* **independence of the lift**: two continuous `2`-cochains with the same image under `π` differ by
  `ι ∘ k` for a continuous `2`-cochain `k` with values in `M` (since their difference lies in
  `ker π = range ι`), and `d²` of the lift differs by `ι (d² k)`; pulling back along `ι` turns this
  into `d² k`, a `3`-coboundary.  Hence the classes of `deltaCocycle3Of` agree;
* **coboundaries go to zero**: if `c = d¹ b` for a continuous `1`-cochain `b`, the canonical lift of
  `c` differs from `d¹ (lift b)` by a constant (hence continuous) cochain, whose `d²` is a
  `3`-coboundary, while `d² ∘ d¹ = 0` kills the `deltaCocycle3Of` of `d¹ (lift b)`.

With `deltaH3` in hand the arithmetic input of the local Euler characteristic enters as
`Subsingleton (H³(G,M))`: then `ker deltaH3 = ⊤`, so the exactness at `H²(G,P)` gives that
`H²(G,N) → H²(G,P)` is surjective, which is what the additivity of `[H⁰][H²]/[H¹]` needs.
-/

open scoped Classical

universe u v

namespace Work.SSGRoute

open Work.AbsoluteKummer

variable {G : Type u} [TopologicalSpace G] [Group G]
  {A B : Type v} [AddCommGroup A] [DistribMulAction G A]
  [AddCommGroup B] [DistribMulAction G B]

/-! ## Functoriality of `d¹` and `d²` -/

/-- `d²` commutes with an equivariant additive map of coefficients. -/
theorem d2_comp (φ : A →+ B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
    (c : G × G → A) :
    Work.GroupCohomology.d2 G B (fun p => φ (c p))
      = fun p => φ (Work.GroupCohomology.d2 G A c p) := by
  funext p
  obtain ⟨g, h, k⟩ := p
  simp only [Work.GroupCohomology.d2_apply, map_sub, map_add, hφ]

/-- `d² ∘ d¹ = 0`. -/
theorem d2_d1_eq_zero (b : G → A) :
    Work.GroupCohomology.d2 G A (Work.GroupCohomology.d1 G A b) = 0 := by
  funext p
  obtain ⟨g, h, k⟩ := p
  simp only [Work.GroupCohomology.d2_apply, Work.GroupCohomology.d1_apply, Pi.zero_apply,
    smul_sub, smul_add, mul_smul, mul_assoc, neg_smul, one_smul]
  abel

end Work.SSGRoute

namespace Work.AbsoluteKummer.ShortExactSeq

open Work.AbsoluteKummer

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

/-! ## The connecting `3`-cochain of an arbitrary continuous lift -/

/-- The connecting `3`-cochain of a continuous `2`-cochain `ñ` with values in `N`: apply `d²` and
pull back along `ι` (`0` where the values are not in `range ι`; for the lifts of a `2`-cocycle
they always are). -/
noncomputable def deltaCochain3 (S : ShortExactSeq G M N P) (ñ : G × G → N) :
    G × G × G → M :=
  fun p => S.iotaInv (Work.GroupCohomology.d2 G N ñ p)

@[simp] theorem deltaCochain3_apply (S : ShortExactSeq G M N P) (ñ : G × G → N)
    (p : G × G × G) :
    S.deltaCochain3 ñ p = S.iotaInv (Work.GroupCohomology.d2 G N ñ p) := rfl

/-- If `π ∘ ñ` is a `2`-cocycle then `π` kills `d²ñ`, so `d²ñ` takes values in `range ι`. -/
theorem pi_d2_of_d2_pi_eq_zero (S : ShortExactSeq G M N P) {ñ : G × G → N}
    (hπ : Work.GroupCohomology.d2 G P (fun p => S.pi (ñ p)) = 0) (p : G × G × G) :
    Work.GroupCohomology.d2 G N ñ p ∈ S.iota.range := by
  rw [S.range_iota_eq_ker_pi, AddMonoidHom.mem_ker]
  rw [← congrFun (Work.SSGRoute.d2_comp S.pi S.pi_equivariant ñ) p]
  exact congrFun hπ p

/-- `range ι = ker π`. -/
theorem mem_ker_of_mem_range (S : ShortExactSeq G M N P) {b : N} (hb : b ∈ S.iota.range) :
    b ∈ S.pi.ker := by
  rwa [← S.range_iota_eq_ker_pi]

/-- **The connecting `3`-cocycle of a continuous lift.**  If `ñ` is a continuous `2`-cochain whose
push-forward along `π` is a `2`-cocycle, then `deltaCochain3 ñ` is a continuous `3`-cocycle. -/
theorem deltaCochain3_mem_Z3 (S : ShortExactSeq G M N P) {ñ : G × G → N}
    (hloc : Work.AbsoluteKummer.IsLocallyConstant ñ)
    (hπ : Work.GroupCohomology.d2 G P (fun p => S.pi (ñ p)) = 0) :
    S.deltaCochain3 ñ ∈ Work.SSGRoute.Z3 (M := M) G := by
  have hmem : ∀ p : G × G × G,
      Work.GroupCohomology.d2 G N ñ p ∈ S.iota.range := pi_d2_of_d2_pi_eq_zero S hπ
  have hfix : (fun p : G × G × G => S.iota (S.deltaCochain3 ñ p))
      = Work.GroupCohomology.d2 G N ñ := by
    funext p
    exact S.iota_iotaInv (hmem p)
  refine ⟨?_, ?_⟩
  · have hcomp : (fun p : G × G × G × G =>
        S.iota (Work.SSGRoute.d3 (S.deltaCochain3 ñ) p))
        = Work.SSGRoute.d3 (fun p : G × G × G => S.iota (S.deltaCochain3 ñ p)) :=
      (Work.SSGRoute.d3_comp S.iota S.iota_equivariant (S.deltaCochain3 ñ)).symm
    have h1 : (fun p : G × G × G × G =>
        S.iota (Work.SSGRoute.d3 (S.deltaCochain3 ñ) p)) = 0 := by
      rw [hcomp, hfix]
      exact Work.SSGRoute.d3_d2 (G := G) (A := N) _
    funext p
    exact S.iota_injective (by
      have h := congrFun h1 p
      simpa using h)
  · exact Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv
      (Work.SSGRoute.isLocallyConstant_d2 S.isDiscreteN hloc)

/-- `deltaZ3` is `deltaCochain3` of the canonical lift. -/
theorem deltaZ3_eq_deltaCochain3 (S : ShortExactSeq G M N P) (c : Z2 G P) :
    S.deltaZ3 c = S.deltaCochain3 (S.liftCochain2 (c : G × G → P)) := rfl

/-! ## Independence of the lift -/

/-- **The connecting cocycle is independent of the lift, modulo `3`-coboundaries.**  If two
continuous `2`-cochains have the same image under `π` and that image is a `2`-cocycle, then the
difference of their connecting cochains is a `3`-coboundary. -/
theorem deltaCochain3_sub_mem_B3 (S : ShortExactSeq G M N P) {ñ ñ' : G × G → N}
    (hloc : Work.AbsoluteKummer.IsLocallyConstant ñ)
    (hloc' : Work.AbsoluteKummer.IsLocallyConstant ñ')
    (hπ : ∀ p : G × G, S.pi (ñ p) = S.pi (ñ' p))
    (hc : Work.GroupCohomology.d2 G P (fun p => S.pi (ñ p)) = 0) :
    (S.deltaCochain3 ñ - S.deltaCochain3 ñ') ∈ Work.SSGRoute.B3 (M := M) G := by
  -- the difference of the two lifts is `ι` of a continuous `2`-cochain `k`
  set k : G × G → M := fun p => S.iotaInv (ñ p - ñ' p) with hk
  have hk_loc : Work.AbsoluteKummer.IsLocallyConstant k :=
    Work.AbsoluteKummer.IsLocallyConstant.map S.iotaInv (hloc.sub hloc')
  have hmem : ∀ p : G × G, ñ p - ñ' p ∈ S.iota.range := by
    intro p
    rw [S.range_iota_eq_ker_pi, AddMonoidHom.mem_ker, map_sub, hπ p, sub_self]
  have hdiff : ∀ p : G × G, ñ p - ñ' p = S.iota (k p) := by
    intro p
    rw [hk]
    exact (S.iota_iotaInv (hmem p)).symm
  have hker : ∀ p : G × G × G, Work.GroupCohomology.d2 G N ñ' p ∈ S.pi.ker := by
    intro p
    rw [AddMonoidHom.mem_ker,
      ← congrFun (Work.SSGRoute.d2_comp S.pi S.pi_equivariant ñ') p,
      show (fun q => S.pi (ñ' q)) = fun q => S.pi (ñ q) from funext fun q => (hπ q).symm]
    exact congrFun hc p
  have hkey : S.deltaCochain3 ñ - S.deltaCochain3 ñ'
      = fun p => S.iotaInv (Work.GroupCohomology.d2 G N ñ' p
          + Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) p)
        - S.iotaInv (Work.GroupCohomology.d2 G N ñ' p) := by
    funext p
    have hd : ñ - ñ' = fun q => S.iota (k q) := funext fun q => hdiff q
    have hsub : Work.GroupCohomology.d2 G N ñ
        = Work.GroupCohomology.d2 G N ñ' + Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) := by
      rw [← hd, map_sub]
      abel
    show S.iotaInv (Work.GroupCohomology.d2 G N ñ p) - S.iotaInv (Work.GroupCohomology.d2 G N ñ' p)
      = S.iotaInv (Work.GroupCohomology.d2 G N ñ' p
          + Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) p)
        - S.iotaInv (Work.GroupCohomology.d2 G N ñ' p)
    rw [show Work.GroupCohomology.d2 G N ñ p
        = Work.GroupCohomology.d2 G N ñ' p
          + Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) p from congrFun hsub p]
  rw [hkey]
  -- the difference is `d² k`, a `3`-coboundary
  rw [Work.SSGRoute.mem_B3_iff (G := G) (M := M)]
  refine ⟨k, hk_loc, ?_⟩
  funext p
  obtain ⟨g, h, l⟩ := p
  have h₁ : Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) (g, h, l)
      = S.iota (Work.GroupCohomology.d2 G M k (g, h, l)) :=
    congrFun (Work.SSGRoute.d2_comp S.iota S.iota_equivariant k) (g, h, l)
  have hker2 : Work.GroupCohomology.d2 G N (fun q => S.iota (k q)) (g, h, l) ∈ S.pi.ker := by
    rw [AddMonoidHom.mem_ker, h₁, S.pi_iota]
  rw [S.iotaInv_add (hker (g, h, l)) hker2, h₁, S.iotaInv_iota]
  abel

/-! ## Additivity of `deltaCochain3` on sums of lifts, and the class-level consequences -/

/-- `deltaCochain3` is additive on sums of continuous lifts whose push-forwards are cocycles. -/
theorem deltaCochain3_add (S : ShortExactSeq G M N P) {ñ ñ' : G × G → N}
    (hπ : Work.GroupCohomology.d2 G P (fun p => S.pi (ñ p)) = 0)
    (hπ' : Work.GroupCohomology.d2 G P (fun p => S.pi (ñ' p)) = 0) :
    S.deltaCochain3 ñ + S.deltaCochain3 ñ' = S.deltaCochain3 (ñ + ñ') := by
  funext p
  show S.iotaInv (Work.GroupCohomology.d2 G N ñ p)
      + S.iotaInv (Work.GroupCohomology.d2 G N ñ' p)
    = S.iotaInv (Work.GroupCohomology.d2 G N (ñ + ñ') p)
  have h1 : Work.GroupCohomology.d2 G N (ñ + ñ') p
      = Work.GroupCohomology.d2 G N ñ p + Work.GroupCohomology.d2 G N ñ' p := by
    rw [map_add]
    rfl
  rw [h1, S.iotaInv_add (S.mem_ker_of_mem_range (pi_d2_of_d2_pi_eq_zero S hπ p))
    (S.mem_ker_of_mem_range (pi_d2_of_d2_pi_eq_zero S hπ' p))]

/-- **The connecting map is additive modulo `3`-coboundaries** (in `H³`). -/
theorem deltaZ3_add_class (S : ShortExactSeq G M N P) (c c' : Z2 G P) :
    Work.SSGRoute.H3π G (S.deltaZ3 (c + c'))
      = Work.SSGRoute.H3π G (S.deltaZ3 c) + Work.SSGRoute.H3π G (S.deltaZ3 c') := by
  have hπ : ∀ p : G × G, S.pi (S.liftCochain2 ((c + c') : G × G → P) p)
      = S.pi ((S.liftCochain2 (c : G × G → P) + S.liftCochain2 (c' : G × G → P)) p) := by
    intro p
    have h1 : S.pi (S.liftCochain2 ((c + c') : G × G → P) p) = ((c + c') : G × G → P) p :=
      pi_liftCochain2 S _ p
    have h2 : S.pi ((S.liftCochain2 (c : G × G → P) + S.liftCochain2 (c' : G × G → P)) p)
        = (c : G × G → P) p + (c' : G × G → P) p := by
      rw [Pi.add_apply, map_add, pi_liftCochain2, pi_liftCochain2]
    rw [h1, h2, Pi.add_apply]
  have hc : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 ((c + c') : G × G → P) p)) = 0 := by
    rw [show (fun p => S.pi (S.liftCochain2 ((c + c') : G × G → P) p))
        = ((c + c') : G × G → P) from funext fun p => pi_liftCochain2 S _ p]
    exact Work.SSGRoute.d2_eq_zero_of_mem_Z2 (c + c').2.1
  have hB : (S.deltaCochain3 (S.liftCochain2 ((c + c') : G × G → P))
        - S.deltaCochain3 (S.liftCochain2 (c : G × G → P) + S.liftCochain2 (c' : G × G → P)))
      ∈ Work.SSGRoute.B3 (M := M) G :=
    S.deltaCochain3_sub_mem_B3
      (isLocallyConstant_liftCochain2 S (c + c').2.2)
      ((isLocallyConstant_liftCochain2 S c.2.2).add (isLocallyConstant_liftCochain2 S c'.2.2))
      hπ hc
  have hπc : Work.GroupCohomology.d2 G P (fun p => S.pi (S.liftCochain2 (c : G × G → P) p)) = 0 := by
    rw [show (fun p => S.pi (S.liftCochain2 (c : G × G → P) p)) = (c : G × G → P)
      from funext fun p => pi_liftCochain2 S _ p]
    exact Work.SSGRoute.d2_eq_zero_of_mem_Z2 c.2.1
  have hπc' : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 (c' : G × G → P) p)) = 0 := by
    rw [show (fun p => S.pi (S.liftCochain2 (c' : G × G → P) p)) = (c' : G × G → P)
      from funext fun p => pi_liftCochain2 S _ p]
    exact Work.SSGRoute.d2_eq_zero_of_mem_Z2 c'.2.1
  -- identify the Z³-elements with `deltaCochain3` of the two lifts
  have hcoe : ((S.deltaZ3 (c + c') - (S.deltaZ3 c + S.deltaZ3 c') : Work.SSGRoute.Z3 (M := M) G)
      : G × G × G → M)
      = S.deltaCochain3 (S.liftCochain2 ((c + c') : G × G → P))
        - S.deltaCochain3 (S.liftCochain2 (c : G × G → P) + S.liftCochain2 (c' : G × G → P)) := by
    funext p
    change S.deltaCochain3 (S.liftCochain2 ((c + c') : G × G → P)) p
        - (S.deltaCochain3 (S.liftCochain2 (c : G × G → P)) p
          + S.deltaCochain3 (S.liftCochain2 (c' : G × G → P)) p)
      = S.deltaCochain3 (S.liftCochain2 ((c + c') : G × G → P)) p
        - S.deltaCochain3 (S.liftCochain2 (c : G × G → P)
          + S.liftCochain2 (c' : G × G → P)) p
    have hp := congrFun (S.deltaCochain3_add hπc hπc') p
    rw [Pi.add_apply] at hp
    rw [hp]
  have h0 : Work.SSGRoute.H3π G (S.deltaZ3 (c + c') - (S.deltaZ3 c + S.deltaZ3 c')) = 0 :=
    (Work.SSGRoute.H3π_eq_zero_iff G _).mpr (hcoe ▸ hB)
  rw [map_sub, map_add, sub_eq_zero] at h0
  exact h0

/-! ## Coboundaries go to zero, and the descended connecting map -/

/-- **Coboundaries go to zero.**  For a continuous `1`-cochain `b` with values in `P`, the class of
the connecting cocycle of the `2`-coboundary `d¹ b` vanishes.  The canonical lift of `d¹ b` is
compared with `d¹ (liftCochainC b)`: the two have the same image under `π`, so their connecting
cochains differ by a `3`-coboundary (`deltaCochain3_sub_mem_B3`), and the connecting cochain of
`d¹ (liftCochainC b)` is `0` because `d² ∘ d¹ = 0`. -/
theorem H3π_deltaZ3_d1 (S : ShortExactSeq G M N P) {b : G → P}
    (hb : Work.AbsoluteKummer.IsLocallyConstant b)
    (hZ : Work.GroupCohomology.d1 G P b ∈ Work.GroupCohomology.Z2 G P) :
    Work.SSGRoute.H3π G (S.deltaZ3 ⟨Work.GroupCohomology.d1 G P b, hZ,
      Work.AbsoluteKummer.isLocallyConstant_d1 S.isDiscreteP hb⟩) = 0 := by
  rw [Work.SSGRoute.H3π_eq_zero_iff G]
  have hπ : ∀ p : G × G, S.pi (S.liftCochain2 (Work.GroupCohomology.d1 G P b) p)
      = S.pi (Work.GroupCohomology.d1 G N (S.liftCochainC b) p) := by
    rintro ⟨g, h⟩
    rw [pi_liftCochain2]
    show Work.GroupCohomology.d1 G P b (g, h)
      = S.pi (Work.GroupCohomology.d1 G N (S.liftCochainC b) (g, h))
    rw [Work.GroupCohomology.d1_apply, Work.GroupCohomology.d1_apply, map_add, map_sub,
      S.pi_equivariant, S.pi_liftCochainC, S.pi_liftCochainC, S.pi_liftCochainC]
  have hc : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 (Work.GroupCohomology.d1 G P b) p)) = 0 := by
    rw [show (fun p => S.pi (S.liftCochain2 (Work.GroupCohomology.d1 G P b) p))
        = Work.GroupCohomology.d1 G P b from funext fun p => pi_liftCochain2 S _ p]
    exact Work.SSGRoute.d2_d1_eq_zero b
  have hzero : S.deltaCochain3 (Work.GroupCohomology.d1 G N (S.liftCochainC b)) = 0 := by
    funext p
    show S.iotaInv (Work.GroupCohomology.d2 G N
      (Work.GroupCohomology.d1 G N (S.liftCochainC b)) p) = 0
    rw [show Work.GroupCohomology.d2 G N (Work.GroupCohomology.d1 G N (S.liftCochainC b)) p = 0
      from congrFun (Work.SSGRoute.d2_d1_eq_zero (S.liftCochainC b)) p, S.iotaInv_zero]
  have hB := S.deltaCochain3_sub_mem_B3
    (isLocallyConstant_liftCochain2 S
      (Work.AbsoluteKummer.isLocallyConstant_d1 S.isDiscreteP hb))
    (Work.AbsoluteKummer.isLocallyConstant_d1 S.isDiscreteN
      (S.isLocallyConstant_liftCochainC hb))
    hπ hc
  rw [hzero, sub_zero] at hB
  exact hB

/-- **The connecting cocycle of a `2`-coboundary has vanishing class**: this is the well-definedness
half of the descent, deduced from the coboundary case `H3π_deltaZ3_d1`. -/
theorem H3π_deltaZ3_of_mem_B2 (S : ShortExactSeq G M N P) {c : Z2 G P}
    (hc : (c : G × G → P) ∈ B2 G P) :
    Work.SSGRoute.H3π G (S.deltaZ3 c) = 0 := by
  have hx : (c : G × G → P) ∈ AddSubgroup.map (Work.GroupCohomology.d1 G P) (C1c G P) := hc
  rw [AddSubgroup.mem_map] at hx
  obtain ⟨b, hb, hbc⟩ := hx
  have h := S.H3π_deltaZ3_d1 hb (hbc ▸ c.2.1)
  rwa [show (⟨Work.GroupCohomology.d1 G P b, hbc ▸ c.2.1,
      Work.AbsoluteKummer.isLocallyConstant_d1 S.isDiscreteP (by simpa using hb)⟩ : Z2 G P) = c
    from Subtype.ext hbc] at h

/-- **The descended connecting map** `deltaH3 : H²(G,P) →+ H³(G,M)`, characterised by agreeing with
`H3π ∘ deltaZ3` on the classes of `2`-cocycles (`deltaH3_H2π`). -/
noncomputable def deltaH3 (S : ShortExactSeq G M N P) :
    H2 G P →+ Work.SSGRoute.H3 (M := M) G :=
  QuotientAddGroup.lift ((B2 G P).comap (Z2 G P).subtype)
    { toFun := fun c => Work.SSGRoute.H3π G (S.deltaZ3 c)
      map_zero' := S.H3π_deltaZ3_of_mem_B2 (B2 G P).zero_mem
      map_add' := fun c c' => S.deltaZ3_add_class c c' }
    (by
      intro x hx
      rw [AddSubgroup.mem_comap] at hx
      exact S.H3π_deltaZ3_of_mem_B2 hx)

theorem deltaH3_H2π (S : ShortExactSeq G M N P) (c : Z2 G P) :
    S.deltaH3 (H2π G P c) = Work.SSGRoute.H3π G (S.deltaZ3 c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Work.AbsoluteKummer.ShortExactSeq
