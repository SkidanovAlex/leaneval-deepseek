import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliaries for `Work.SSGRoute.local_kummer_dies`

A "Kummer datum" over a group `G`: a short exact sequence
`0 → 𝔽_p → A → A^p → 0` together with the quotient sequence `0 → A^p → A → A/A^p → 0`.
The main engine lemma factors any `x ∈ H²(G, 𝔽_p)` killed under `z_*` through the two connecting
maps.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

section Generic

variable {G : Type} [Group G]

/-- A Kummer datum over `G`: the Kummer sequence `0 → 𝔽_p → A → P → 0` (with `P = A^p`) together
with the quotient sequence `0 → P → A → Q → 0` (with `Q = A/A^p`). -/
structure KummerDatum (p : ℕ) [Fact p.Prime] (G : Type) [Group G] where
  A : Rep.{0} Coeff G
  P : Rep.{0} Coeff G
  Q : Rep.{0} Coeff G
  z : Rep.trivial Coeff G (ZMod p) ⟶ A
  pth : A ⟶ P
  hz0 : z ≫ pth = 0
  incl : P ⟶ A
  quot : A ⟶ Q
  hiq : incl ≫ quot = 0
  hS1 : (ShortComplex.mk z pth hz0).ShortExact
  hS2 : (ShortComplex.mk incl quot hiq).ShortExact

variable {p : ℕ} [Fact p.Prime] (D : KummerDatum p G)

/-- **The engine.**  If `H¹(G, A) = 0`, then any `x ∈ H²(G, 𝔽_p)` killed by `z_*` is the image of
an element of `H⁰(G, A/A^p)` under the composite connecting map `∂ ∘ ∂'`. -/
theorem kummerDatum_factor
    (hA1 : Subsingleton (extH D.A 1))
    (x : extH (Rep.trivial Coeff G (ZMod p)) 2)
    (hx : x.comp (Abelian.Ext.mk₀ D.z) (add_zero 2) = 0) :
    ∃ b : extH D.Q 0,
      x = (b.comp D.hS2.extClass (zero_add 1)).comp D.hS1.extClass (by norm_num) := by
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ (X := unitRep G)
    (S := ShortComplex.mk D.z D.pth D.hz0) D.hS1 x hx (n₀ := 1) (by norm_num)
  have hy0 : y.comp (Abelian.Ext.mk₀ D.incl) (add_zero 1) = 0 := Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₁ (X := unitRep G)
    (S := ShortComplex.mk D.incl D.quot D.hiq) D.hS2 y hy0 (n₀ := 0) (by norm_num)
  exact ⟨b, by rw [← hy, ← hb]⟩

end Generic

set_option backward.isDefEq.respectTransparency false

section Naturality

variable {G H : Type} [Group G] [Group H]

/-- **Naturality of the connecting map `extClass` of a short exact sequence under a change of
group.**  For a morphism `φ : S.map (Rep.resFunctor g) ⟶ S'` of short complexes over `H` compared
with a short exact complex `S` over `G`, inflating the Yoneda product `y.comp S.extClass` along `g`
(with coefficient map `φ.τ₁`) is the Yoneda product of the inflation of `y` (coefficient map
`φ.τ₃`) with the connecting class `S'.extClass`. -/
theorem extHMap_comp_extClass (g : H →* G)
    {S : ShortComplex (Rep.{0} Coeff G)} (hS : S.ShortExact)
    {S' : ShortComplex (Rep.{0} Coeff H)} (hS' : S'.ShortExact)
    (φ : S.map (Rep.resFunctor g) ⟶ S') {r : ℕ} (y : extH S.X₃ r) :
    extHMap g φ.τ₁ (y.comp hS.extClass rfl) = (extHMap g φ.τ₃ y).comp hS'.extClass rfl := by
  have hmap : (S.map (Rep.resFunctor g)).ShortExact := hS.map_of_exact (Rep.resFunctor g)
  have hnat := ShortComplex.ShortExact.extClass_naturality hmap hS' φ
  have heq : hS.extClass.mapExactFunctor (Rep.resFunctor g) = hmap.extClass :=
    Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor g) hS
  simp only [extHMap, extRes, Abelian.Ext.mapExactFunctor_comp, heq]
  rw [E6Util.comp_assoc_of_first_deg_zero]
  congr 1
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, hnat,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero]

end Naturality

section Hom

variable {p : ℕ} [Fact p.Prime] {G H : Type} [Group G] [Group H] (g : H →* G)
  (D : KummerDatum p G) (D' : KummerDatum p H)

/-- A morphism of Kummer data along `g : H →* G`: compatible coefficient maps on `A`, `A^p` and
`A/A^p` and on the trivial module `𝔽_p`. -/
structure KummerDatumHom where
  iA : Rep.res g D.A ⟶ D'.A
  iP : Rep.res g D.P ⟶ D'.P
  iQ : Rep.res g D.Q ⟶ D'.Q
  iz : Rep.res g (Rep.trivial Coeff G (ZMod p)) ⟶ Rep.trivial Coeff H (ZMod p)
  sq1 : Rep.resMap g D.z ≫ iA = iz ≫ D'.z
  sq2 : Rep.resMap g D.pth ≫ iP = iA ≫ D'.pth
  sq3 : Rep.resMap g D.incl ≫ iA = iP ≫ D'.incl
  sq4 : Rep.resMap g D.quot ≫ iQ = iA ≫ D'.quot

/-- **The naturality of the two-step Kummer decomposition.**  If `x` is the image of `b ∈ H⁰(G,A/A^p)`
under `∂ ∘ ∂'` and the image of `b` at the higher level is `0`, then so is the image of `x`. -/
theorem kummerDatumHom_extHMap (F : KummerDatumHom g D D') (b : extH D.Q 0)
    (hb : extHMap g F.iQ b = 0) :
    extHMap g F.iz ((b.comp D.hS2.extClass (zero_add 1)).comp D.hS1.extClass rfl) = 0 := by
  have key1 := extHMap_comp_extClass g D.hS1 D'.hS1
    (ShortComplex.homMk F.iz F.iA F.iP
      (by simp only [ShortComplex.map_f]; exact F.sq1.symm)
      (by simp only [ShortComplex.map_g]; exact F.sq2.symm))
    (y := b.comp D.hS2.extClass (zero_add 1))
  have key2 := extHMap_comp_extClass g D.hS2 D'.hS2
    (ShortComplex.homMk F.iP F.iA F.iQ
      (by simp only [ShortComplex.map_f]; exact F.sq3.symm)
      (by simp only [ShortComplex.map_g]; exact F.sq4.symm))
    (y := b)
  rw [show extHMap g F.iz ((b.comp D.hS2.extClass (zero_add 1)).comp D.hS1.extClass rfl)
      = (extHMap g F.iP (b.comp D.hS2.extClass (zero_add 1))).comp D'.hS1.extClass rfl
      from key1,
    show extHMap g F.iP (b.comp D.hS2.extClass (zero_add 1))
      = (extHMap g F.iQ b).comp D'.hS2.extClass (zero_add 1) from key2,
    hb]
  simp only [Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

end Hom

section Concrete

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-! ### Elementary group-theoretic helpers -/

/-- In an abelian group with `p • x = 0`, an `n` coprime to `p` satisfying `n • x = 0` forces
`x = 0`. -/
theorem eq_zero_of_nsmul_eq_zero_of_coprime {A : Type*} [AddCommGroup A] {p : ℕ} {x : A}
    (hpx : p • x = 0) {n : ℕ} (hn : n.Coprime p) (hnx : n • x = 0) : x = 0 := by
  have hbez := Nat.gcd_eq_gcd_ab n p
  have hgcd : (Nat.gcd n p : ℤ) = 1 := by rw [hn.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA n p : ℤ) * (n : ℤ) + (Nat.gcdB n p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA n p) (n : ℤ), mul_comm (Nat.gcdB n p) (p : ℤ)]
    exact hbez.symm
  have hx : x = (Nat.gcdA n p * (n : ℤ) + Nat.gcdB n p * (p : ℤ)) • x := by
    rw [hbez', one_smul]
  rw [hx, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hnx, hpx, smul_zero,
    smul_zero, add_zero]

/-- The `n`-th additive multiple of `Additive.ofMul u` is `Additive.ofMul (u ^ n)`. -/
theorem nsmul_ofMul_eq (F : Type) [DivInvMonoid F] (n : ℕ) (u : F) :
    n • (Additive.ofMul u) = Additive.ofMul (u ^ n) := by
  rw [← natCast_zsmul, ← zpow_natCast]
  exact (ofMul_zpow (n : ℤ) u).symm

/-- `n • (z • v) = z • (n • v)` in an additive commutative group. -/
theorem nsmul_zsmul_comm {A : Type*} [AddCommGroup A] (n : ℕ) (z : ℤ) (v : A) :
    n • (z • v) = z • (n • v) := by
  rw [← natCast_zsmul (z • v) n, ← natCast_zsmul v n, ← mul_smul, ← mul_smul,
    mul_comm z (n : ℤ)]

/-! ### The `p`-th powers of the local units -/

/-- The `p`-th powers `(K_wˣ)^p` of the local units `K_wˣ`, as a `Coeff`-submodule. -/
noncomputable def localPthSub (w : NK.GlobalCFT.Place K) (p : ℕ) :
    Submodule Coeff (localUnitsK (k := k) w) :=
  LinearMap.range ((p : ℕ) •
    (LinearMap.id : localUnitsK (k := k) w →ₗ[Coeff] localUnitsK (k := k) w))

theorem mem_localPthSub_iff (w : NK.GlobalCFT.Place K) (p : ℕ)
    (x : localUnitsK (k := k) w) :
    x ∈ localPthSub k K w p ↔ ∃ u : localUnitsK (k := k) w, (p : ℕ) • u = x :=
  LinearMap.mem_range

/-- `(K_wˣ)^p` is stable under `D_w`. -/
theorem localPthSub_mem_rho (w : NK.GlobalCFT.Place K) (p : ℕ) (γ : decompK (k := k) w)
    {x : localUnitsK (k := k) w} (hx : x ∈ localPthSub k K w p) :
    (localUnitsK (k := k) w).ρ γ x ∈ localPthSub k K w p := by
  obtain ⟨u, rfl⟩ := (mem_localPthSub_iff k K w p x).mp hx
  exact (mem_localPthSub_iff k K w p _).mpr
    ⟨(localUnitsK (k := k) w).ρ γ u, (map_nsmul ((localUnitsK (k := k) w).ρ γ) p u).symm⟩

noncomputable instance instSMulLocalPthSub (w : NK.GlobalCFT.Place K) (p : ℕ) :
    SMul (decompK (k := k) w) ↥(localPthSub k K w p) where
  smul γ x := ⟨(localUnitsK (k := k) w).ρ γ (x : localUnitsK (k := k) w),
    localPthSub_mem_rho k K w p γ x.2⟩

noncomputable instance instDistribMulActionLocalPthSub (w : NK.GlobalCFT.Place K) (p : ℕ) :
    DistribMulAction (decompK (k := k) w) ↥(localPthSub k K w p) where
  one_smul x := Subtype.ext (by
    show (localUnitsK (k := k) w).ρ (1 : decompK (k := k) w)
      (x : localUnitsK (k := k) w) = (x : localUnitsK (k := k) w)
    simp [map_one])
  mul_smul γ δ x := Subtype.ext (by
    show (localUnitsK (k := k) w).ρ (γ * δ) (x : localUnitsK (k := k) w)
      = (localUnitsK (k := k) w).ρ γ ((localUnitsK (k := k) w).ρ δ
          (x : localUnitsK (k := k) w))
    rw [map_mul]
    rfl)
  smul_zero γ := Subtype.ext (by
    show (localUnitsK (k := k) w).ρ γ (0 : localUnitsK (k := k) w) = 0
    rw [map_zero])
  smul_add γ x y := Subtype.ext (by
    show (localUnitsK (k := k) w).ρ γ ((x : localUnitsK (k := k) w)
        + (y : localUnitsK (k := k) w))
      = (localUnitsK (k := k) w).ρ γ (x : localUnitsK (k := k) w)
        + (localUnitsK (k := k) w).ρ γ (y : localUnitsK (k := k) w)
    rw [map_add])

/-! ### The Kummer quotient `K_wˣ ⧸ (K_wˣ)^p` -/

/-- The action of `D_w` on the quotient `K_wˣ ⧸ (K_wˣ)^p`, as a `Coeff`-linear map. -/
noncomputable def localKummerQuotSmul (w : NK.GlobalCFT.Place K) (p : ℕ)
    (γ : decompK (k := k) w) :
    (localUnitsK (k := k) w ⧸ localPthSub k K w p) →ₗ[Coeff]
      (localUnitsK (k := k) w ⧸ localPthSub k K w p) :=
  (localPthSub k K w p).liftQ
    ((Submodule.mkQ (localPthSub k K w p)).comp ((localUnitsK (k := k) w).ρ γ))
    (fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact localPthSub_mem_rho k K w p γ hx)

noncomputable instance instSMulLocalKummerQuot (w : NK.GlobalCFT.Place K) (p : ℕ) :
    SMul (decompK (k := k) w) (localUnitsK (k := k) w ⧸ localPthSub k K w p) where
  smul γ := localKummerQuotSmul k K w p γ

theorem localKummerQuotSmul_comp_mkQ (w : NK.GlobalCFT.Place K) (p : ℕ)
    (γ : decompK (k := k) w) :
    (localKummerQuotSmul k K w p γ).comp (Submodule.mkQ (localPthSub k K w p))
      = (Submodule.mkQ (localPthSub k K w p)).comp ((localUnitsK (k := k) w).ρ γ) :=
  Submodule.liftQ_mkQ _ _ _

theorem localKummerQuotSmul_eq_of_comp_mkQ (w : NK.GlobalCFT.Place K) (p : ℕ)
    {f g : (localUnitsK (k := k) w ⧸ localPthSub k K w p) →ₗ[Coeff]
      (localUnitsK (k := k) w ⧸ localPthSub k K w p)}
    (h : f.comp (Submodule.mkQ (localPthSub k K w p))
      = g.comp (Submodule.mkQ (localPthSub k K w p))) : f = g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (localPthSub k K w p) x
  exact LinearMap.congr_fun h a

theorem localKummerQuot_smul_mk (w : NK.GlobalCFT.Place K) (p : ℕ)
    (γ : decompK (k := k) w) (a : localUnitsK (k := k) w) :
    γ • (Submodule.mkQ (localPthSub k K w p) a)
      = Submodule.mkQ (localPthSub k K w p) ((localUnitsK (k := k) w).ρ γ a) := by
  show localKummerQuotSmul k K w p γ (Submodule.mkQ (localPthSub k K w p) a) = _
  rw [← LinearMap.comp_apply, localKummerQuotSmul_comp_mkQ]
  rfl

theorem localKummerQuot_smul_zero (w : NK.GlobalCFT.Place K) (p : ℕ)
    (γ : decompK (k := k) w) :
    γ • (0 : localUnitsK (k := k) w ⧸ localPthSub k K w p) = 0 :=
  map_zero (localKummerQuotSmul k K w p γ)

theorem localKummerQuot_smul_add (w : NK.GlobalCFT.Place K) (p : ℕ)
    (γ : decompK (k := k) w) (x y : localUnitsK (k := k) w ⧸ localPthSub k K w p) :
    γ • (x + y) = γ • x + γ • y :=
  map_add (localKummerQuotSmul k K w p γ) x y

noncomputable instance instDistribMulActionLocalKummerQuot (w : NK.GlobalCFT.Place K) (p : ℕ) :
    DistribMulAction (decompK (k := k) w) (localUnitsK (k := k) w ⧸ localPthSub k K w p) where
  one_smul x := by
    show localKummerQuotSmul k K w p 1 x = x
    rw [show localKummerQuotSmul k K w p 1 = LinearMap.id from
      localKummerQuotSmul_eq_of_comp_mkQ k K w p (by
        rw [localKummerQuotSmul_comp_mkQ, map_one]
        rfl)]
    rfl
  mul_smul γ δ x := by
    show localKummerQuotSmul k K w p (γ * δ) x
      = localKummerQuotSmul k K w p γ (localKummerQuotSmul k K w p δ x)
    rw [show localKummerQuotSmul k K w p (γ * δ)
        = (localKummerQuotSmul k K w p γ).comp (localKummerQuotSmul k K w p δ) from
      localKummerQuotSmul_eq_of_comp_mkQ k K w p (by
        rw [LinearMap.comp_assoc, localKummerQuotSmul_comp_mkQ,
          localKummerQuotSmul_comp_mkQ, ← LinearMap.comp_assoc, map_mul]
        rfl)]
    rfl
  smul_zero := localKummerQuot_smul_zero k K w p
  smul_add := localKummerQuot_smul_add k K w p

/-! ### The representations and the two short exact sequences -/

-- `(K_wˣ)^p` as a `D_w`-representation.
abbrev localPthRep (w : NK.GlobalCFT.Place K) (p : ℕ) :
    Rep Coeff (decompK (k := k) w) :=
  modRep (decompK (k := k) w) ↥(localPthSub k K w p)

-- `K_wˣ ⧸ (K_wˣ)^p` as a `D_w`-representation.
abbrev localKummerQuot (w : NK.GlobalCFT.Place K) (p : ℕ) :
    Rep Coeff (decompK (k := k) w) :=
  modRep (decompK (k := k) w) (localUnitsK (k := k) w ⧸ localPthSub k K w p)

/-- The `p`-th power map `K_wˣ ⟶ (K_wˣ)^p`. -/
noncomputable def localPthMap (w : NK.GlobalCFT.Place K) (p : ℕ) :
    localUnitsK (k := k) w ⟶ localPthRep k K w p :=
  Rep.ofHom
    { toFun := fun v => ⟨(p : ℕ) • v, LinearMap.mem_range_self _ v⟩
      map_add' := fun a b => Subtype.ext (smul_add (p : ℕ) a b)
      map_smul' := fun c v => Subtype.ext (by
        show (p : ℕ) • (c • v) = c • ((p : ℕ) • v)
        rw [ULift.smul_def, ULift.smul_def]
        exact nsmul_zsmul_comm p c.down v)
      isIntertwining' := fun γ => by
        apply LinearMap.ext
        intro v
        exact Subtype.ext (by
          show (p : ℕ) • ((localUnitsK (k := k) w).ρ γ (v : localUnitsK (k := k) w))
            = (localUnitsK (k := k) w).ρ γ ((p : ℕ) • (v : localUnitsK (k := k) w))
          rw [map_nsmul]) }

@[simp]
theorem localPthMap_apply (w : NK.GlobalCFT.Place K) (p : ℕ)
    (v : localUnitsK (k := k) w) :
    (localPthMap k K w p).hom v = ⟨(p : ℕ) • v, LinearMap.mem_range_self _ v⟩ := rfl

/-- The inclusion `(K_wˣ)^p ⟶ K_wˣ`. -/
noncomputable def localPthIncl (w : NK.GlobalCFT.Place K) (p : ℕ) :
    localPthRep k K w p ⟶ localUnitsK (k := k) w :=
  Rep.ofHom
    { toFun := fun v => (v : localUnitsK (k := k) w)
      map_add' := fun a b => rfl
      map_smul' := fun c v => rfl
      isIntertwining' := fun γ => by
        apply LinearMap.ext
        intro v
        rfl }

@[simp]
theorem localPthIncl_apply (w : NK.GlobalCFT.Place K) (p : ℕ)
    (v : ↥(localPthSub k K w p)) :
    (localPthIncl k K w p).hom v = (v : localUnitsK (k := k) w) := rfl

/-- The quotient map `K_wˣ ⟶ K_wˣ ⧸ (K_wˣ)^p`. -/
noncomputable def localKummerQuotMap (w : NK.GlobalCFT.Place K) (p : ℕ) :
    localUnitsK (k := k) w ⟶ localKummerQuot k K w p :=
  Rep.ofHom
    { toFun := fun v => Submodule.mkQ (localPthSub k K w p) v
      map_add' := fun a b => Submodule.Quotient.mk_add (localPthSub k K w p)
      map_smul' := fun c v => rfl
      isIntertwining' := fun γ => by
        apply LinearMap.ext
        intro v
        exact (localKummerQuot_smul_mk k K w p γ v).symm }

@[simp]
theorem localKummerQuotMap_apply (w : NK.GlobalCFT.Place K) (p : ℕ)
    (v : localUnitsK (k := k) w) :
    (localKummerQuotMap k K w p).hom v = Submodule.mkQ (localPthSub k K w p) v := rfl

end Concrete


end

end Work.SSGRoute
