import Mathlib.Tactic.Group
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Submission.Work.SSGRoute.PT.exists_cocycle_on_quotient_of_vanishing_on_both_vars
import Submission.Work.SSGRoute.PT.exists_primitive_vanishing_on_normal_both_vars
import Submission.Work.SSGRoute.PT.exists_primitive_vanishing_on_proPrimeToP
import Submission.Work.SSGRoute.PT.quotient_proCyclicGrowth
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Pointwise

/-- **Local constancy is preserved when subtracting the coboundary of a locally constant
`1`-cochain.**  If `c` is locally constant on `Γ × Γ`, `b` locally constant on `Γ` and the action
of `Γ` (through `act`) on `M` is trivial on an open subgroup, then
`(g,h) ↦ c g h - (act g • b h - b (g*h) + b g)` is locally constant.

The key point is that the local-constancy subgroups may be replaced by their normal cores, so
that `(g*u)*(h*v) = (g*h)*((h⁻¹*u*h)*v)` with `h⁻¹*u*h` again in the subgroup. -/
theorem zd_isLocConst2_sub_cob2d
    {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group G] [AddCommGroup M] [DistribMulAction G M]
    (act : Γ →* G) (c : Γ → Γ → M) (b : Γ → M)
    (hlc : SSGRoute.IsLocConst2 c) (hlb : SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) b)
    (hker : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ U₀ ≤ act.ker) :
    SSGRoute.IsLocConst2 (fun g h => c g h - (act g • b h - b (g * h) + b g)) := by
  obtain ⟨Uc, hUcopen, hUcinv⟩ := hlc
  obtain ⟨Ub, hUbopen, hUbinv⟩ := hlb
  obtain ⟨U₀, hU₀open, hU₀le⟩ := hker
  have hKopen : IsOpen (((Uc ⊓ Ub) ⊓ U₀ : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (hUcopen.inter hUbopen).inter hU₀open
  have hKclosed : IsClosed (((Uc ⊓ Ub) ⊓ U₀ : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_of_isOpen _ hKopen
  haveI hKfin : (((Uc ⊓ Ub) ⊓ U₀ : Subgroup Γ)).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen _ hKopen
  set U : Subgroup Γ := (((Uc ⊓ Ub) ⊓ U₀ : Subgroup Γ)).normalCore with hUdef
  haveI hUn : U.Normal := by rw [hUdef]; exact Subgroup.normalCore_normal _
  haveI hUfin : U.FiniteIndex := by rw [hUdef]; infer_instance
  have hUle : U ≤ (Uc ⊓ Ub) ⊓ U₀ := by rw [hUdef]; exact Subgroup.normalCore_le _
  have hUopen : IsOpen (U : Set Γ) := by
    rw [hUdef]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ hKclosed)
  refine ⟨U, hUopen, ?_⟩
  intro g h x y hx hy
  have hxUc : x ∈ Uc := (hUle hx).1.1
  have hxUb : x ∈ Ub := (hUle hx).1.2
  have hyUb : y ∈ Ub := (hUle hy).1.2
  have hxU₀ : x ∈ U₀ := (hUle hx).2
  have hyUc : y ∈ Uc := (hUle hy).1.1
  have hconj : h⁻¹ * x * h ∈ U := by
    simpa using hUn.conj_mem x hx h⁻¹
  have hxy : (h⁻¹ * x * h) * y ∈ Ub := Ub.mul_mem (hUle hconj).1.2 hyUb
  have h1 : c (g * x) (h * y) = c g h := hUcinv g h x y hxUc hyUc
  have h2 : act (g * x) = act g := by
    rw [map_mul, show act x = 1 from MonoidHom.mem_ker.mp (hU₀le hxU₀), mul_one]
  have h3 : b (h * y) = b h := hUbinv h (Subgroup.mem_top h) y hyUb (Subgroup.mem_top y)
  have h4 : b (g * x) = b g := hUbinv g (Subgroup.mem_top g) x hxUb (Subgroup.mem_top x)
  have h5 : b ((g * x) * (h * y)) = b (g * h) := by
    have hrew : (g * x) * (h * y) = (g * h) * ((h⁻¹ * x * h) * y) := by group
    rw [hrew]
    exact hUbinv (g * h) (Subgroup.mem_top (g * h)) _ hxy (Subgroup.mem_top _)
  show c (g * x) (h * y) - (act (g * x) • b (h * y) - b ((g * x) * (h * y)) + b (g * x))
      = c g h - (act g • b h - b (g * h) + b g)
  rw [h1, h2, h3, h4, h5]


/-- **The `H²`-vanishing input for the inertia of a finite place** (pro-prime-to-`p` normal subgroup `V` with pro-cyclically growing quotient): if `V ◁ Γ` is closed and pro-prime-to-`p`, `Γ` is compact, `Γ/V` has all finite quotients cyclic (`hcyc`) and every open normal `K ≥ V` contains an open normal `L ≥ V` with `p ∣ [K : L]` (`hbig`), and the action of `Γ` on the finite `𝔽_p`-module `N` factors through a homomorphism `act` with open kernel, then every locally constant `2`-cocycle `c` on `Γ` is a coboundary of a locally constant `1`-cochain. A correct route (the naive "extend the primitive on `V` by zero" does NOT work, because vanishing of `c₁` on `V × V` gives no control over `c₁ x v` for `x ∉ V`): choose an open normal `U ≤ act.ker` with `c` invariant under `U` (`hkerG`, `IsLocConst2`), so that both `c` and the whole problem live on the finite group `Q = Γ/U`; then `W = VU/U ≅ V/(V ∩ U)` is normal in `Q` of order prime to `p` (`hpro`), `Q/W` is a quotient of `Γ/V` hence pro-cyclic with the growth property (`hcyc`, `hbig`), `H²(W,N) = 0` by averaging (`Work.SSGRoute.isCoboundary2On_top_of_isProPrimeToP`), and `H²(Q/W, N^W) = 0` by the pro-cyclic growth vanishing (`Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth`); the descent/inflation bookkeeping (double averaging, `Work.SSGRoute.dlt`, `descentInflationFinite.lean`, `PT.exists_primitive_vanishing_on_proPrimeToP`) assembles the primitive. -/
theorem zhat_descent_proPrimeToP_proCyclicGrowth
    (p : ℕ) [Fact p.Prime]
    {Γ G N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [Group G] [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N]
    (V : Subgroup Γ) [V.Normal] (hVclosed : IsClosed (V : Set Γ))
    (hpro : NK.LocalTame.IsProPrimeToP p ↥V)
    (act : Γ →* G)
    (hkerG : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ U₀ ≤ act.ker)
    (hcyc : ∀ (K : Subgroup Γ) [K.Normal], V ≤ K → K.FiniteIndex → IsCyclic (Γ ⧸ K))
    (hbig : ∀ (K : Subgroup Γ) [K.Normal], V ≤ K → IsOpen (K : Set Γ) →
      ∃ (L : Subgroup Γ) (hL : L.Normal), V ≤ L ∧ L ≤ K ∧ IsOpen (L : Set Γ) ∧
        p ∣ (L.subgroupOf K).index)
    (c : Γ → Γ → N) (hc : _root_.SSGRoute.IsCocycle2 act c)
    (hlc : _root_.SSGRoute.IsLocConst2 c) :
    _root_.SSGRoute.IsCoboundary2On act ⊤ c := by
  classical
  -- ## Step 1: a primitive of `c` on `Γ × V` (vanishing of `H²(V,N)`)
  obtain ⟨b₀, hb₀loc, hb₀⟩ :=
    PT.exists_primitive_vanishing_on_proPrimeToP p act V (inferInstance : V.Normal) hVclosed hpro
      c hc hlc
  -- ## Step 2: `c₁ := c - δb₀` vanishes on `Γ × V`
  let c₁ : Γ → Γ → N := fun g h => c g h - (act g • b₀ h - b₀ (g * h) + b₀ g)
  have hc₁ : SSGRoute.IsCocycle2 act c₁ :=
    cob2_isCocycle2_sub (act := act) hc (cob2d_isCocycle act b₀)
  have hc₁loc : SSGRoute.IsLocConst2 c₁ :=
    zd_isLocConst2_sub_cob2d act c b₀ hlc hb₀loc hkerG
  have hc₁van : ∀ g : Γ, ∀ v ∈ V, c₁ g v = 0 := by
    intro g v hv
    have h := hb₀ g v hv
    show c g v - (act g • b₀ v - b₀ (g * v) + b₀ g) = 0
    rw [h]; abel
  -- ## Step 3: view `N` as a `Γ`-module through `act`
  letI : DistribMulAction Γ N := DistribMulAction.compHom N act
  haveI hcomm : SMulCommClass Γ (ZMod p) N := ⟨fun g r n => smul_comm (act g) r n⟩
  have hsmul : ∀ (g : Γ) (n : N), g • n = act g • n := fun g n => rfl
  have hc₁id : SSGRoute.IsCocycle2 (MonoidHom.id Γ) c₁ := by
    intro g h l
    have h := hc₁ g h l
    simpa only [MonoidHom.id_apply, hsmul] using h
  have hkerΓ : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ ∀ g ∈ U₀, ∀ n : N, g • n = n := by
    obtain ⟨U₀, hU₀open, hU₀le⟩ := hkerG
    exact ⟨U₀, hU₀open, fun g hg n => by
      rw [hsmul g n, show act g = 1 from MonoidHom.mem_ker.mp (hU₀le hg), one_smul]⟩
  -- ## Step 4: adjust the primitive so that `c` is killed on `V × Γ` as well
  obtain ⟨u, huloc, hu1, hu2⟩ :=
    PT.exists_primitive_vanishing_on_normal_both_vars p V (inferInstance : V.Normal) hVclosed hpro
      hkerΓ c₁ hc₁id hc₁loc hc₁van
  have hu1' : ∀ g : Γ, ∀ v ∈ V, c₁ g v = act g • u v - u (g * v) + u g := by
    intro g v hv
    rw [← hsmul g (u v)]
    exact hu1 g v hv
  have hu2' : ∀ v ∈ V, ∀ h : Γ, c₁ v h = act v • u h - u (v * h) + u v := by
    intro v hv h
    rw [← hsmul v (u h)]
    exact hu2 v hv h
  -- ## Step 5: `c₂ := c₁ - δu` vanishes on both `Γ × V` and `V × Γ`, and is locally constant
  let c₂ : Γ → Γ → N := fun g h => c₁ g h - (act g • u h - u (g * h) + u g)
  have hc₂act : SSGRoute.IsCocycle2 act c₂ :=
    cob2_isCocycle2_sub (act := act) hc₁ (cob2d_isCocycle act u)
  have hc₂ : SSGRoute.IsCocycle2 (MonoidHom.id Γ) c₂ := by
    intro g h l
    have h := hc₂act g h l
    simpa only [MonoidHom.id_apply, hsmul] using h
  have hc₂loc : SSGRoute.IsLocConst2 c₂ :=
    zd_isLocConst2_sub_cob2d act c₁ u hc₁loc huloc hkerG
  have hc₂van1 : ∀ g : Γ, ∀ v ∈ V, c₂ g v = 0 := by
    intro g v hv
    have hh := hu1' g v hv
    show c₁ g v - (act g • u v - u (g * v) + u g) = 0
    rw [hh]; abel
  have hc₂van2 : ∀ v ∈ V, ∀ h : Γ, c₂ v h = 0 := by
    intro v hv h
    have hh := hu2' v hv h
    show c₁ v h - (act v • u h - u (v * h) + u v) = 0
    rw [hh]; abel
  -- ## Step 6: descend `c₂` to a cocycle on `Γ ⧸ V` with values in the fixed points `N^V`
  obtain ⟨c₀, hc₀coc, hc₀loc, hc₀eq⟩ :=
    PT.exists_cocycle_on_quotient_of_vanishing_on_both_vars p V (inferInstance : V.Normal)
      c₂ hc₂ hc₂loc hc₂van1 hc₂van2
  -- ## Step 7: the pro-cyclicity and growth hypotheses descend to `Γ ⧸ V`
  obtain ⟨hcyc', hbig'⟩ := PT.quotient_proCyclicGrowth p V hcyc hbig
  have hkerQ : ∃ U₀' : Subgroup (Γ ⧸ V), IsOpen (U₀' : Set (Γ ⧸ V)) ∧
      ∀ g ∈ U₀', ∀ n : ↥(PT.fixedPoints p N V), g • n = n := by
    obtain ⟨U₀, hU₀open, hU₀le⟩ := hkerG
    refine ⟨U₀.map (QuotientGroup.mk' V), ?_, ?_⟩
    · have hmk : (QuotientGroup.mk' V : Γ → Γ ⧸ V) = QuotientGroup.mk :=
        funext (QuotientGroup.mk'_apply V)
      have h : IsOpen ((QuotientGroup.mk : Γ → Γ ⧸ V) '' (U₀ : Set Γ)) :=
        QuotientGroup.isOpenQuotientMap_mk.isOpenMap (U₀ : Set Γ) hU₀open
      simpa only [Subgroup.coe_map, hmk] using h
    · intro q hq n
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
      refine Subtype.ext ?_
      rw [PT.smul_fixedPoints_coe, PT.quotientActionHom_mk_apply]
      show g • ((n : ↥(PT.fixedPoints p N V)) : N) = ((n : ↥(PT.fixedPoints p N V)) : N)
      rw [hsmul g ((n : ↥(PT.fixedPoints p N V)) : N),
        show act g = 1 from MonoidHom.mem_ker.mp (hU₀le hg), one_smul]
  -- ## Step 8: pro-cyclic growth vanishing on `Γ ⧸ V` with coefficients `N^V`
  obtain ⟨b₁, hb₁loc, hb₁eq⟩ :=
    Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth (p := p)
      (Γ := Γ ⧸ V) (G := Γ ⧸ V) (N := ↥(PT.fixedPoints p N V))
      (MonoidHom.id (Γ ⧸ V)) hcyc' hkerQ hbig' c₀ hc₀coc hc₀loc
  -- ## Step 9: assemble the primitive `b₀ + u + b₁ ∘ π`
  refine ⟨fun g => b₀ g + u g + ((b₁ (QuotientGroup.mk' V g) :
      ↥(PT.fixedPoints p N V)) : N), ?_, ?_⟩
  · obtain ⟨Ua, hUaopen, hUa⟩ := hb₀loc
    obtain ⟨Ub, hUbopen, hUb⟩ := huloc
    obtain ⟨Uc, hUcopen, hUc⟩ := hb₁loc
    have hcont : Continuous (QuotientGroup.mk' V : Γ → Γ ⧸ V) := by
      rw [show (QuotientGroup.mk' V : Γ → Γ ⧸ V) = QuotientGroup.mk from
        funext (QuotientGroup.mk'_apply V)]
      exact QuotientGroup.continuous_mk
    refine ⟨(Ua ⊓ Ub) ⊓ Uc.comap (QuotientGroup.mk' V), ?_, ?_⟩
    · rw [Subgroup.coe_inf, Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hUaopen.inter hUbopen).inter (hUcopen.preimage hcont)
    · intro g _ x hx _
      rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx
      obtain ⟨⟨hxa, hxb⟩, hxc⟩ := hx
      have h1 : b₀ (g * x) = b₀ g := hUa g (Subgroup.mem_top g) x hxa (Subgroup.mem_top x)
      have h2 : u (g * x) = u g := hUb g (Subgroup.mem_top g) x hxb (Subgroup.mem_top x)
      have h3 : b₁ (QuotientGroup.mk' V (g * x)) = b₁ (QuotientGroup.mk' V g) := by
        rw [map_mul]
        exact hUc (QuotientGroup.mk' V g) (Subgroup.mem_top _) (QuotientGroup.mk' V x) hxc
          (Subgroup.mem_top _)
      show b₀ (g * x) + u (g * x)
          + ((b₁ (QuotientGroup.mk' V (g * x)) : ↥(PT.fixedPoints p N V)) : N)
        = b₀ g + u g + ((b₁ (QuotientGroup.mk' V g) : ↥(PT.fixedPoints p N V)) : N)
      rw [h1, h2, h3]
  · intro g _ h _
    have hb₁ := hb₁eq (QuotientGroup.mk' V g) (Subgroup.mem_top _) (QuotientGroup.mk' V h)
      (Subgroup.mem_top _)
    have hb₁N : ((c₀ (QuotientGroup.mk' V g) (QuotientGroup.mk' V h) :
            ↥(PT.fixedPoints p N V)) : N)
        = act g • (((b₁ (QuotientGroup.mk' V h) :
              ↥(PT.fixedPoints p N V)) : N))
          - (((b₁ (QuotientGroup.mk' V (g * h)) :
              ↥(PT.fixedPoints p N V)) : N))
          + (((b₁ (QuotientGroup.mk' V g) :
              ↥(PT.fixedPoints p N V)) : N)) := by
      have hh := congrArg (fun x : ↥(PT.fixedPoints p N V) => (x : N)) hb₁
      simp only [Submodule.coe_sub, Submodule.coe_add, MonoidHom.id_apply,
        PT.smul_fixedPoints_coe, PT.quotientActionHom_mk_apply, hsmul, ← map_mul] at hh
      exact hh
    have h1 : c g h = c₁ g h + (act g • b₀ h - b₀ (g * h) + b₀ g) := by
      show c g h = (c g h - (act g • b₀ h - b₀ (g * h) + b₀ g))
        + (act g • b₀ h - b₀ (g * h) + b₀ g)
      abel
    have h2 : c₁ g h = c₂ g h + (act g • u h - u (g * h) + u g) := by
      show c₁ g h = (c₁ g h - (act g • u h - u (g * h) + u g))
        + (act g • u h - u (g * h) + u g)
      abel
    have h3 : c₂ g h = ((c₀ (QuotientGroup.mk' V g) (QuotientGroup.mk' V h) :
        ↥(PT.fixedPoints p N V)) : N) := hc₀eq g h
    rw [h1, h2, h3, hb₁N]
    simp only [smul_add]
    abel

end Work.SSGRoute
