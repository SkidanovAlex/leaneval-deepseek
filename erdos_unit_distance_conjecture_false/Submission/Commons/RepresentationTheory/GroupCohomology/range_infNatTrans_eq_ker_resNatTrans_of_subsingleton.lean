import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Submission.Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1

/-!
# Inflation–restriction exactness in arbitrary degree

This file proves the exactness of the inflation–restriction sequence
`H^r(G ⧸ S, A^S) → H^r(G, A) → H^r(S, A)` under the vanishing hypothesis `H^j(S, A) = 0` for
`0 < j < r`, by *dimension shifting*: one shifts into the cokernel `C` of the canonical
`G`-equivariant map `A ⟶ Coind_⊥^G(A)` and uses the connecting homomorphisms of the long exact
sequences in `G`-, `S`- and `G ⧸ S`-cohomology.

## Main results

* `Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton`

## Design notes

The shift module `Coind_⊥^G(-)` is acyclic for `G`, for any subgroup `S ≤ G` and, after taking
`S`-invariants, for the quotient `G ⧸ S` (these are Shapiro's lemma for the trivial group together
with the decomposition of `G` as an `S`-set).  This makes the connecting homomorphisms of the three
long exact sequences isomorphisms in the relevant degrees, and these isomorphisms are compatible
with the inflation and restriction maps by the naturality of the connecting homomorphism.
-/

open CategoryTheory CategoryTheory.Limits Representation

namespace Commons.RepresentationTheory.GroupCohomology

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- Any function `H → M` lies in the submodule of `H`-equivariant functions defining the
coinduction from the trivial subgroup. -/
lemma mem_coindV_bot {H : Type u} [Group H] {M : Type u} [AddCommGroup M] [Module k M]
    (σ : Representation k (⊥ : Subgroup H) M) (f : H → M) :
    f ∈ Representation.coindV (⊥ : Subgroup H).subtype σ := by
  rw [Representation.mem_coindV]
  intro g h
  rw [show g = 1 from Subsingleton.elim g 1]
  simp

noncomputable section

namespace InfResAux

/-- Coinduction from the trivial subgroup of `G` of a representation of the trivial group. -/
abbrev MG (A : Rep.{u,u,u} k (⊥ : Subgroup G)) : Rep.{u,u,u} k G :=
  Rep.coind (⊥ : Subgroup G).subtype A

/-- The underlying function of an element of `Coind_⊥^G(A)`. -/
def mgFun (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (x : (MG A).V) : G → A.V := x.1

@[simp]
lemma mgFun_apply (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (x : (MG A).V) (g : G) :
    mgFun A x g = (x.1 : G → A.V) g := rfl

/-- The action of `Coind_⊥^G(A)`. -/
lemma MG_rho_apply (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (g : G) (x : (MG A).V) :
    mgFun A ((MG A).ρ g x) = fun y => mgFun A x (y * g) := rfl

/-- `Coind_⊥^G(M)` for a `G`-representation `M` (regarded as a representation of the trivial
group). -/
def shiftI (M : Rep.{u,u,u} k G) : Rep.{u,u,u} k G := MG (Rep.res (⊥ : Subgroup G).subtype M)

@[simp]
lemma shiftI_def (M : Rep.{u,u,u} k G) :
    shiftI M = Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype M) := rfl

/-- The underlying linear map of the canonical map `M ⟶ Coind_⊥^G(M)`, `m ↦ (g ↦ g • m)`. -/
def shiftUnitLin (M : Rep.{u,u,u} k G) : M.V →ₗ[k] (shiftI M).V :=
  (LinearMap.pi (fun g : G => M.ρ g)).codRestrict _ (fun _ => mem_coindV_bot _ _)

@[simp]
lemma shiftUnitLin_apply (M : Rep.{u,u,u} k G) (m : M.V) (g : G) :
    (shiftUnitLin M m).1 g = M.ρ g m := rfl

/-- The canonical `G`-map `M ⟶ Coind_⊥^G(M)`. -/
def shiftUnit (M : Rep.{u,u,u} k G) : M ⟶ shiftI M :=
  Rep.ofHom { shiftUnitLin M with
    isIntertwining' g := LinearMap.ext (fun m => by
      apply Subtype.ext
      funext x
      show M.ρ x (M.ρ g m) = (shiftUnitLin M m).1 (x * g)
      rw [shiftUnitLin_apply, ← Module.End.mul_apply, ← map_mul]) }

@[simp]
lemma shiftUnit_hom_toLinearMap (M : Rep.{u,u,u} k G) :
    (shiftUnit M).hom.toLinearMap = shiftUnitLin M := rfl

lemma shiftUnit_injective (M : Rep.{u,u,u} k G) : Function.Injective (shiftUnit M).hom := by
  intro m m' h
  have h2 : shiftUnitLin M m = shiftUnitLin M m' := h
  have h3 : (shiftUnitLin M m).1 1 = (shiftUnitLin M m').1 1 :=
    congrFun (congrArg Subtype.val h2) 1
  rw [shiftUnitLin_apply, shiftUnitLin_apply] at h3
  simpa using h3

lemma shiftUnitLin_comm (M : Rep.{u,u,u} k G) (g : G) (m : M.V) :
    shiftUnitLin M (M.ρ g m) = (shiftI M).ρ g (shiftUnitLin M m) := by
  have h := LinearMap.congr_fun ((shiftUnit M).hom.isIntertwining' g) m
  simp only [shiftUnit_hom_toLinearMap, LinearMap.comp_apply] at h
  exact h

/-- The cokernel of `M ⟶ Coind_⊥^G(M)`. -/
def shiftC (M : Rep.{u,u,u} k G) : Rep.{u,u,u} k G := cokernel (shiftUnit M)

/-- The short complex `0 → M → Coind_⊥^G(M) → C → 0`. -/
def shiftX (M : Rep.{u,u,u} k G) : ShortComplex (Rep.{u,u,u} k G) :=
  ShortComplex.mk (shiftUnit M) (cokernel.π (shiftUnit M)) (cokernel.condition _)

@[simp]
lemma shiftX_f (M : Rep.{u,u,u} k G) : (shiftX M).f = shiftUnit M := rfl

@[simp]
lemma shiftX_g (M : Rep.{u,u,u} k G) : (shiftX M).g = cokernel.π (shiftUnit M) := rfl

lemma shiftX_exact (M : Rep.{u,u,u} k G) : (shiftX M).Exact :=
  ShortComplex.exact_of_g_is_cokernel (shiftX M) (cokernelIsCokernel (shiftUnit M))

lemma shiftX_shortExact (M : Rep.{u,u,u} k G) : (shiftX M).ShortExact := by
  refine ShortComplex.ShortExact.mk' (shiftX_exact M) ?_ ?_
  · rw [shiftX_f]
    exact (Rep.mono_iff_injective _).mpr (shiftUnit_injective M)
  · exact inferInstanceAs (Epi (cokernel.π (shiftUnit M)))

lemma forget_map_hom {A B : Rep.{u,u,u} k G} (f : A ⟶ B) :
    ModuleCat.Hom.hom ((forget₂ (Rep.{u,u,u} k G) (ModuleCat k)).map f) = f.hom.toLinearMap := rfl

lemma shiftX_range_eq_ker (M : Rep.{u,u,u} k G) :
    LinearMap.range (shiftUnitLin M) =
      LinearMap.ker ((cokernel.π (shiftUnit M)).hom.toLinearMap) := by
  have hex : ((shiftX M).map (forget₂ (Rep.{u,u,u} k G) (ModuleCat k))).Exact :=
    (ShortComplex.exact_map_iff_of_faithful (shiftX M) (forget₂ (Rep.{u,u,u} k G) (ModuleCat k))).mpr
      (shiftX_exact M)
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hex
  change LinearMap.range (ModuleCat.Hom.hom ((forget₂ (Rep.{u,u,u} k G) (ModuleCat k)).map (shiftUnit M)))
      = LinearMap.ker (ModuleCat.Hom.hom ((forget₂ (Rep.{u,u,u} k G) (ModuleCat k)).map
          (cokernel.π (shiftUnit M)))) at h
  rw [forget_map_hom, forget_map_hom, shiftUnit_hom_toLinearMap] at h
  exact h

lemma shiftUnitLin_mem_ker (M : Rep.{u,u,u} k G) (m : M.V) :
    shiftUnitLin M m ∈ LinearMap.ker ((cokernel.π (shiftUnit M)).hom.toLinearMap) := by
  have h : shiftUnitLin M m ∈ LinearMap.range (shiftUnitLin M) := LinearMap.mem_range_self _ m
  rwa [shiftX_range_eq_ker M] at h

lemma cokernel_pi_shiftUnitLin (M : Rep.{u,u,u} k G) (m : M.V) :
    (cokernel.π (shiftUnit M)).hom (shiftUnitLin M m) = 0 :=
  shiftUnitLin_mem_ker M m


/-- Shapiro's lemma for the trivial subgroup: cohomology of a representation coinduced from the
trivial subgroup vanishes in positive degrees. -/
lemma isZero_coind_bot {H : Type u} [Group H] (A : Rep.{u,u,u} k (⊥ : Subgroup H)) (n : ℕ) :
    IsZero (groupCohomology (Rep.coind (⊥ : Subgroup H).subtype A) (n + 1)) := by
  have hsub : Subsingleton (⊥ : Subgroup H) :=
    ⟨fun a b => Subtype.ext (by rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hz : IsZero (groupCohomology A (n + 1)) :=
    @isZero_groupCohomology_succ_of_subsingleton k (⊥ : Subgroup H) _ _ hsub A n
  exact IsZero.of_iso hz (groupCohomology.coindIso A (n + 1))

section

variable (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G))

noncomputable abbrev coindQuotCoeff (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (S : Subgroup G) [S.Normal] :
    Rep.{u,u,u} k (⊥ : Subgroup S) :=
  Rep.trivial k (⊥ : Subgroup S) (G ⧸ S → A.V)

noncomputable abbrev coindResCoind (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (S : Subgroup G) [S.Normal] :
    Rep.{u,u,u} k S :=
  Rep.coind (⊥ : Subgroup S).subtype (coindQuotCoeff A S)

section

variable (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G))

/-- For `g : G`, an element `s ∈ S` with `c(gS) * s = g`, where `c(gS)` is the chosen
representative of the right coset of `g`. -/
noncomputable def rcosetFactor (g : G) : S :=
  ⟨(Quotient.out ((g : G) : G ⧸ S))⁻¹ * g, by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S g
    rw [hh]
    have : (g * (h : G))⁻¹ * g = (h : G)⁻¹ := by group
    rw [this]
    exact S.inv_mem h.2⟩

lemma rcosetRep_mul_factor (g : G) :
    Quotient.out ((g : G) : G ⧸ S) * (rcosetFactor S g : G) = g := by
  simp [rcosetFactor]

lemma rcosetFactor_rep_mul (q : G ⧸ S) (s : S) :
    rcosetFactor S (Quotient.out q * (s : G)) = s := by
  apply Subtype.ext
  simp only [rcosetFactor]
  have h : (((Quotient.out q * (s : G) : G)) : G ⧸ S) = q := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq',
      show (((s : G)) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff (s : G)).2 s.2, mul_one]
  rw [h]
  group

/-- The `S`-equivariant bijection `S × G⧸S → G`, `(s, q) ↦ c(q) * s`. -/
noncomputable def rcosetEquiv : S × (G ⧸ S) → G := fun p => Quotient.out p.2 * (p.1 : G)

lemma rcosetEquiv_surj : Function.Surjective (rcosetEquiv S) := by
  intro g
  exact ⟨(rcosetFactor S g, (g : G ⧸ S)), rcosetRep_mul_factor S g⟩

lemma rcosetEquiv_inj : Function.Injective (rcosetEquiv S) := by
  intro p q hp
  simp only [rcosetEquiv] at hp
  have hpS : (((p.1 : S) : G) : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff (p.1 : G)).2 p.1.2
  have hqS : (((q.1 : S) : G) : G ⧸ S) = 1 := (QuotientGroup.eq_one_iff (q.1 : G)).2 q.1.2
  have h2 : p.2 = q.2 := by
    have h3 := congrArg (fun x : G => (x : G ⧸ S)) hp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
      hpS, hqS, mul_one, mul_one] at h3
    exact h3
  have h1 : (p.1 : G) = (q.1 : G) := by
    rw [h2] at hp
    exact mul_left_cancel hp
  exact Prod.ext (Subtype.ext h1) h2

lemma rcosetEquiv_bij : Function.Bijective (rcosetEquiv S) :=
  ⟨rcosetEquiv_inj S, rcosetEquiv_surj S⟩

end

section

variable (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G))

noncomputable def toFunS : (MG A).V →ₗ[k] (coindResCoind A S).V where
  toFun x := ⟨fun s q => mgFun A x (Quotient.out q * (s : G)), mem_coindV_bot _ _⟩
  map_add' x y := by apply Subtype.ext; funext s q; rfl
  map_smul' r x := by apply Subtype.ext; funext s q; rfl

noncomputable def psiS : (coindResCoind A S).V →ₗ[k] (MG A).V where
  toFun F := ⟨fun g => F.1 (rcosetFactor S g) ((g : G ⧸ S)), mem_coindV_bot _ _⟩
  map_add' F G := by apply Subtype.ext; funext g; rfl
  map_smul' r F := by apply Subtype.ext; funext g; rfl

lemma left_inv_S (x : (MG A).V) : psiS S A (toFunS S A x) = x := by
  apply Subtype.ext
  funext g
  show mgFun A x (Quotient.out ((g : G) : G ⧸ S) * (rcosetFactor S g : G)) = mgFun A x g
  rw [rcosetRep_mul_factor]

lemma right_inv_S (F : (coindResCoind A S).V) : toFunS S A (psiS S A F) = F := by
  apply Subtype.ext
  funext s q
  show F.1 (rcosetFactor S (Quotient.out q * (s : G)))
      (((Quotient.out q * (s : G) : G)) : G ⧸ S) = F.1 s q
  have h : (((Quotient.out q * (s : G) : G)) : G ⧸ S) = q := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [show (((s : G)) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff (s : G)).2 s.2, mul_one]
  rw [rcosetFactor_rep_mul S q s, h]

noncomputable def linS : (MG A).V ≃ₗ[k] (coindResCoind A S).V where
  toFun := toFunS S A
  invFun := psiS S A
  left_inv := left_inv_S S A
  right_inv := right_inv_S S A
  map_add' := (toFunS S A).map_add
  map_smul' := (toFunS S A).map_smul

lemma linS_apply (x : (MG A).V) (s : S) (q : G ⧸ S) :
    (linS S A x).1 s q = mgFun A x (Quotient.out q * (s : G)) := rfl

lemma linS_equivariant (s : S) :
    (linS S A).toLinearMap ∘ₗ ((Rep.res S.subtype (MG A)).ρ s) =
      (coindResCoind A S).ρ s ∘ₗ (linS S A).toLinearMap := by
  ext x : 1
  apply Subtype.ext
  funext s' q
  show mgFun A x ((Quotient.out q * (s' : G)) * (s : G))
      = mgFun A x (Quotient.out q * ((s' * s : S) : G))
  rw [mul_assoc]
  rfl

end

theorem isZero_groupCohomology_res_coind_bot (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (n : ℕ) :
    IsZero (groupCohomology (Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype A)) (n + 1)) := by
  have hz : IsZero (groupCohomology (coindResCoind A S) (n + 1)) :=
    isZero_coind_bot (coindQuotCoeff A S) n
  refine IsZero.of_iso hz (groupCohomology.mapIso (MulEquiv.refl S) (linS S A)
    (fun s => linS_equivariant S A s) (n + 1))

end

section

variable (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G))

noncomputable abbrev IQ (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (S : Subgroup G) [S.Normal] :
    Rep.{u,u,u} k (G ⧸ S) :=
  (MG A).quotientToInvariants S

noncomputable abbrev BQ (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (S : Subgroup G) [S.Normal] :
    Rep.{u,u,u} k (⊥ : Subgroup (G ⧸ S)) :=
  Rep.trivial k (⊥ : Subgroup (G ⧸ S)) A.V

noncomputable abbrev JQ (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (S : Subgroup G) [S.Normal] :
    Rep.{u,u,u} k (G ⧸ S) :=
  Rep.coind (⊥ : Subgroup (G ⧸ S)).subtype (BQ A S)

section

variable (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G))

lemma IQ_inv (x : (IQ A S).V) (s : S) :
    (fun g : G => mgFun A x.1 (g * (s : G))) = mgFun A x.1 := by
  funext g
  exact congrFun (congrArg (fun z : (MG A).V => mgFun A z) (x.2 s)) g

noncomputable def toFunQ : (IQ A S).V →ₗ[k] (JQ A S).V :=
  ((LinearMap.funLeft k A.V (Quotient.out :
      (G ⧸ S) → G)).comp ((Submodule.subtype _).comp (Submodule.subtype _))).codRestrict _
    (fun _ => mem_coindV_bot _ _)

noncomputable def psi0 : (JQ A S).V →ₗ[k] (MG A).V :=
  ((LinearMap.funLeft k A.V (fun g : G => (g : G ⧸ S))).comp (Submodule.subtype _)).codRestrict _
    (fun _ => mem_coindV_bot _ _)

lemma psi0_inv (F : (JQ A S).V) (s : S) : (MG A).ρ s (psi0 S A F) = psi0 S A F := by
  ext g
  show (F.1 : (G ⧸ S) → A.V) (((g : G) : G ⧸ S) * ((s : G) : G ⧸ S)) = F.1 ((g : G) : G ⧸ S)
  rw [show (((s : G)) : G ⧸ S) = 1 from (QuotientGroup.eq_one_iff (s : G)).2 s.2, mul_one]

noncomputable def toFunQI : (JQ A S).V →ₗ[k] (IQ A S).V :=
  (psi0 S A).codRestrict _ (fun F => psi0_inv S A F)

lemma left_inv_Q (x : (IQ A S).V) : toFunQI S A (toFunQ S A x) = x := by
  ext g
  show mgFun A x.1 (Quotient.out ((g : G) : G ⧸ S)) = mgFun A x.1 g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S g
  rw [hh]
  exact congrFun (IQ_inv S A x h) g

lemma right_inv_Q (F : (JQ A S).V) : toFunQ S A (toFunQI S A F) = F := by
  ext q
  show (toFunQI S A F).1.1 (Quotient.out q) = F.1 q
  show (F.1 : (G ⧸ S) → A.V) (((Quotient.out q : G)) : G ⧸ S) = F.1 q
  rw [QuotientGroup.out_eq' q]

noncomputable def linQ : (IQ A S).V ≃ₗ[k] (JQ A S).V where
  toFun := toFunQ S A
  invFun := toFunQI S A
  left_inv := left_inv_Q S A
  right_inv := right_inv_Q S A
  map_add' := (toFunQ S A).map_add
  map_smul' := (toFunQ S A).map_smul

lemma linQ_apply (x : (IQ A S).V) (q : G ⧸ S) :
    (linQ S A x).1 q = mgFun A x.1 (Quotient.out q) := rfl

lemma linQ_equivariant (q : G ⧸ S) :
    (linQ S A).toLinearMap ∘ₗ (IQ A S).ρ q = (JQ A S).ρ q ∘ₗ (linQ S A).toLinearMap := by
  induction q using QuotientGroup.induction_on with | H g =>
  ext x : 1
  apply Subtype.ext
  funext q'
  show mgFun A x.1 (Quotient.out q' * g) = mgFun A x.1 (Quotient.out (q' * (g : G ⧸ S)))
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S (Quotient.out q' * g)
  have hq : (((Quotient.out q' * g : G)) : G ⧸ S) = q' * (g : G ⧸ S) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [← hq, hh]
  exact (congrFun (IQ_inv S A x h) (Quotient.out q' * g)).symm

end

theorem isZero_groupCohomology_quotientToInvariants_coind_bot (S : Subgroup G) [S.Normal] (A : Rep.{u,u,u} k (⊥ : Subgroup G)) (n : ℕ) :
    IsZero (groupCohomology ((Rep.coind (⊥ : Subgroup G).subtype A).quotientToInvariants S) (n + 1)) := by
  have hz : IsZero (groupCohomology (JQ A S) (n + 1)) :=
    isZero_coind_bot (BQ A S) n
  refine IsZero.of_iso hz (groupCohomology.mapIso (MulEquiv.refl (G ⧸ S)) (linQ S A)
    (fun q => linQ_equivariant S A q) (n + 1))

end

noncomputable section

/-- Surjectivity of `I^S → C^S` (the `Q`-side epimorphism), assuming `H¹(S, M) = 0`. -/
lemma cokernel_quotient_surjective (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal]
    (h1 : Subsingleton (groupCohomology (Rep.res S.subtype M) 1)) :
    Function.Surjective (((Rep.quotientToInvariantsFunctor k S).map
      (cokernel.π (shiftUnit M))).hom) := by
  intro y
  obtain ⟨i, hi⟩ := (Rep.epi_iff_surjective (cokernel.π (shiftUnit M))).mp
    (inferInstance : Epi (cokernel.π (shiftUnit M))) y.1
  have hmem : ∀ s : S, ∃ m : M.V, shiftUnitLin M m = (shiftI M).ρ s i - i := by
    intro s
    have h0 : (cokernel.π (shiftUnit M)).hom ((shiftI M).ρ s i - i) = 0 := by
      have hcomm := Rep.hom_comm_apply (cokernel.π (shiftUnit M)) (s : G) i
      have hy : (cokernel (shiftUnit M)).ρ (s : G) y.1 = y.1 := y.2 s
      rw [map_sub, hcomm, hi, hy, sub_self]
    have h1' : (shiftI M).ρ s i - i ∈ LinearMap.ker ((cokernel.π (shiftUnit M)).hom.toLinearMap) :=
      LinearMap.mem_ker.mpr h0
    rw [← shiftX_range_eq_ker M] at h1'
    exact LinearMap.mem_range.mp h1'
  choose mj hmj using hmem
  have hcoc : mj ∈ groupCohomology.cocycles₁ (Rep.res S.subtype M) := by
    rw [groupCohomology.mem_cocycles₁_def]
    intro s t
    apply shiftUnit_injective M
    change shiftUnitLin M (M.ρ (s : G) (mj t) - mj (s * t) + mj s) = shiftUnitLin M 0
    rw [map_zero, map_add, map_sub, shiftUnitLin_comm, hmj t, hmj (s * t), hmj s]
    have hst : (shiftI M).ρ (s : G) ((shiftI M).ρ (t : G) i) = (shiftI M).ρ ((s * t : S) : G) i := by
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul]
    rw [map_sub, hst]
    abel
  obtain ⟨α, hα⟩ :=
    exists_sub_eq_of_subsingleton_H1 S M h1 mj hcoc
  refine ⟨⟨i - shiftUnitLin M α, ?_⟩, ?_⟩
  · rw [Representation.mem_invariants]
    intro s
    have hs : ((shiftI M).ρ.comp S.subtype) s (i - shiftUnitLin M α)
        = (shiftI M).ρ (s : G) (i - shiftUnitLin M α) := rfl
    have h1' : (shiftI M).ρ (s : G) i = shiftUnitLin M (mj s) + i := by
      rw [hmj s]; abel
    have h2' : (shiftI M).ρ (s : G) (shiftUnitLin M α) = shiftUnitLin M (M.ρ (s : G) α) :=
      (shiftUnitLin_comm M (s : G) α).symm
    rw [hs, map_sub, h1', h2', ← hα s, map_sub]
    abel
  · apply Subtype.ext
    show (cokernel.π (shiftUnit M)).hom (i - shiftUnitLin M α) = y.1
    rw [map_sub, hi, cokernel_pi_shiftUnitLin, sub_zero]

lemma quotientToInvariants_map_zero (S : Subgroup G) [S.Normal] {A B : Rep k G} :
    (Rep.quotientToInvariantsFunctor k S).map (0 : A ⟶ B) = 0 := by
  apply Rep.hom_ext
  ext x
  apply Subtype.ext
  show (0 : A ⟶ B).hom x.1 = 0
  simp

/-- The `Q`-side short complex `M^S → I^S → C^S`. -/
def shiftXQ (M : Rep k G) (S : Subgroup G) [S.Normal] : ShortComplex (Rep k (G ⧸ S)) :=
  ShortComplex.mk ((Rep.quotientToInvariantsFunctor k S).map (shiftUnit M))
    ((Rep.quotientToInvariantsFunctor k S).map (cokernel.π (shiftUnit M)))
    (by rw [← Functor.map_comp, cokernel.condition, quotientToInvariants_map_zero])

@[simp]
lemma shiftXQ_f (M : Rep k G) (S : Subgroup G) [S.Normal] :
    (shiftXQ M S).f = (Rep.quotientToInvariantsFunctor k S).map (shiftUnit M) := rfl
@[simp]
lemma shiftXQ_g (M : Rep k G) (S : Subgroup G) [S.Normal] :
    (shiftXQ M S).g = (Rep.quotientToInvariantsFunctor k S).map (cokernel.π (shiftUnit M)) := rfl

@[simp]
lemma quotientToInvariants_map_apply {A B : Rep k G} (S : Subgroup G) [S.Normal] (f : A ⟶ B)
    (x : (A.quotientToInvariants S).V) :
    (((Rep.quotientToInvariantsFunctor k S).map f).hom x).1 = f.hom x.1 := rfl

lemma shiftXQ_range_eq_ker (M : Rep k G) (S : Subgroup G) [S.Normal] :
    LinearMap.range ((shiftXQ M S).f.hom.toLinearMap)
      = LinearMap.ker ((shiftXQ M S).g.hom.toLinearMap) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (cokernel.π (shiftUnit M)).hom ((shiftUnit M).hom w.1) = 0
    exact cokernel_pi_shiftUnitLin M w.1
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz' : (cokernel.π (shiftUnit M)).hom z.1 = 0 := congrArg Subtype.val hz
    have hzmem : z.1 ∈ LinearMap.ker ((cokernel.π (shiftUnit M)).hom.toLinearMap) := hz'
    rw [← shiftX_range_eq_ker M] at hzmem
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hzmem
    have hminv2 : ∀ s : S, M.ρ (s : G) m = m := by
      intro s
      apply shiftUnit_injective M
      change shiftUnitLin M (M.ρ (s : G) m) = shiftUnitLin M m
      rw [shiftUnitLin_comm, hm]
      exact z.2 s
    refine ⟨⟨m, ?_⟩, ?_⟩
    · rw [Representation.mem_invariants]
      intro s
      exact hminv2 s
    · apply Subtype.ext
      exact hm

lemma shiftXQ_shortExact (M : Rep k G) (S : Subgroup G) [S.Normal]
    (h1 : Subsingleton (groupCohomology (Rep.res S.subtype M) 1)) :
    (shiftXQ M S).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.exact_map_iff_of_faithful (shiftXQ M S)
      (forget₂ (Rep k (G ⧸ S)) (ModuleCat k))).mp ?_
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (ModuleCat.Hom.hom ((forget₂ (Rep k (G ⧸ S)) (ModuleCat k)).map
        (shiftXQ M S).f)) = LinearMap.ker (ModuleCat.Hom.hom
        ((forget₂ (Rep k (G ⧸ S)) (ModuleCat k)).map (shiftXQ M S).g))
    rw [forget_map_hom, forget_map_hom]
    exact shiftXQ_range_eq_ker M S
  · rw [Rep.mono_iff_injective]
    intro x y hxy
    apply Subtype.ext
    apply shiftUnit_injective M
    exact congrArg Subtype.val hxy
  · rw [Rep.epi_iff_surjective]
    exact cokernel_quotient_surjective M S h1

/-! ### The three short exact sequences of cochain complexes -/

/-- The `G`-side short exact sequence of cochain complexes. -/
abbrev SG (M : Rep.{u,u,u} k G) : ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  (shiftX M).map (groupCohomology.cochainsFunctor k G)

/-- The `S`-side short exact sequence of cochain complexes. -/
abbrev SS (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ((shiftX M).map (Rep.resFunctor S.subtype)).map (groupCohomology.cochainsFunctor k S)

/-- The `Q`-side short exact sequence of cochain complexes. -/
abbrev SQ (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  (shiftXQ M S).map (groupCohomology.cochainsFunctor k (G ⧸ S))

lemma SG_shortExact (M : Rep.{u,u,u} k G) : (SG M).ShortExact :=
  groupCohomology.map_cochainsFunctor_shortExact (shiftX_shortExact M)

lemma SS_shortExact (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] :
    (SS M S).ShortExact :=
  groupCohomology.map_cochainsFunctor_shortExact
    ((Rep.shortExact_res S.subtype).mpr (shiftX_shortExact M))

lemma SQ_shortExact (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal]
    (h1 : Subsingleton (groupCohomology (Rep.res S.subtype M) 1)) :
    (SQ M S).ShortExact :=
  groupCohomology.map_cochainsFunctor_shortExact (shiftXQ_shortExact M S h1)

/-- The morphism of short complexes of cochain complexes given by restricting cochain maps
along a change of groups. -/
noncomputable def phiRes (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] :
    SG M ⟶ SS M S :=
  ShortComplex.homMk
    (groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype (shiftX M).X₁)))
    (groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype (shiftX M).X₂)))
    (groupCohomology.cochainsMap S.subtype (𝟙 (Rep.res S.subtype (shiftX M).X₃)))
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext g
      rfl)
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext g
      rfl)

/-- The morphism of short complexes of cochain complexes given by inflating cochain maps along
`G → G ⧸ S`. -/
noncomputable def phiInf (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] :
    SQ M S ⟶ SG M :=
  ShortComplex.homMk
    (groupCohomology.cochainsMap (QuotientGroup.mk' S)
      (Rep.ofHom (Representation.quotientToInvariants_lift M.ρ S)))
    (groupCohomology.cochainsMap (QuotientGroup.mk' S)
      (Rep.ofHom (Representation.quotientToInvariants_lift (shiftI M).ρ S)))
    (groupCohomology.cochainsMap (QuotientGroup.mk' S)
      (Rep.ofHom (Representation.quotientToInvariants_lift (shiftC M).ρ S)))
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext g
      rfl)
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext g
      rfl)


/-! ### Naturality of the connecting homomorphisms -/

lemma nat_res (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    (HomologicalComplex.homologyMap (phiRes M S).τ₁ (n + 2)).hom.comp
        ((SG_shortExact M).δ (n + 1) (n + 2) rfl).hom
      = ((SS_shortExact M S).δ (n + 1) (n + 2) rfl).hom.comp
        (HomologicalComplex.homologyMap (phiRes M S).τ₃ (n + 1)).hom := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (phiRes M S)
    (SG_shortExact M) (SS_shortExact M S) (n + 1) (n + 2) rfl
  have h2 := congrArg ModuleCat.Hom.hom h
  simpa [ModuleCat.hom_comp] using h2

lemma nat_inf (M : Rep.{u,u,u} k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h1 : Subsingleton (groupCohomology (Rep.res S.subtype M) 1)) :
    (HomologicalComplex.homologyMap (phiInf M S).τ₁ (n + 2)).hom.comp
        ((SQ_shortExact M S h1).δ (n + 1) (n + 2) rfl).hom
      = ((SG_shortExact M).δ (n + 1) (n + 2) rfl).hom.comp
        (HomologicalComplex.homologyMap (phiInf M S).τ₃ (n + 1)).hom := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (phiInf M S)
    (SQ_shortExact M S h1) (SG_shortExact M) (n + 1) (n + 2) rfl
  have h2 := congrArg ModuleCat.Hom.hom h
  simpa [ModuleCat.hom_comp] using h2

end

/-- Dimension-shifting core: if the inflation and restriction maps in degree `r` are obtained
from those in degree `r - 1` by the connecting homomorphisms `α`, `β`, `γ` of the three long
exact sequences, then exactness in degree `r - 1` implies exactness in degree `r`. -/
lemma range_eq_ker_of_shift {R X Y Z W U V : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    [AddCommGroup W] [Module R W] [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (α : X →ₗ[R] Y) (β : Z →ₗ[R] W) (γ : U →ₗ[R] V)
    (infM : V →ₗ[R] Y) (resM : Y →ₗ[R] W) (infC : U →ₗ[R] X) (resC : X →ₗ[R] Z)
    (hα_surj : Function.Surjective α)
    (hβ_inj : Function.Injective β) (hγ_surj : Function.Surjective γ)
    (nat1 : resM.comp α = β.comp resC) (nat2 : infM.comp γ = α.comp infC)
    (ind : LinearMap.range infC = LinearMap.ker resC) :
    LinearMap.range infM = LinearMap.ker resM := by
  have h1 : (infM.comp γ).range = infM.range := by
    rw [LinearMap.range_comp, (LinearMap.range_eq_top).mpr hγ_surj, Submodule.map_top]
  have hker : resC.ker = Submodule.comap α resM.ker := by
    have h := congrArg LinearMap.ker nat1
    rw [LinearMap.ker_comp, LinearMap.ker_comp, (LinearMap.ker_eq_bot).mpr hβ_inj,
      Submodule.comap_bot] at h
    exact h.symm
  calc LinearMap.range infM = (infM.comp γ).range := h1.symm
    _ = (α.comp infC).range := by rw [nat2]
    _ = Submodule.map α infC.range := LinearMap.range_comp infC α
    _ = Submodule.map α resC.ker := by rw [ind]
    _ = Submodule.map α (Submodule.comap α resM.ker) := by rw [hker]
    _ = resM.ker := Submodule.map_comap_eq_self (by rw [(LinearMap.range_eq_top).mpr hα_surj]; exact le_top)

/-- **Inflation–restriction exactness in degree `r`**, in the auxiliary form needed for the
induction (with the coefficient module universally quantified). -/
theorem range_infNatTrans_eq_ker_resNatTrans_aux (S : Subgroup G) [S.Normal] :
    ∀ r, 0 < r → ∀ M : Rep.{u,u,u} k G,
      (∀ j, 0 < j → j < r → Subsingleton (groupCohomology (Rep.res S.subtype M) j)) →
      LinearMap.range ((groupCohomology.infNatTrans k S r).app M).hom =
        LinearMap.ker ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype r).app M).hom := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr M hM
    rcases r with _ | _ | n
    · exact absurd hr (Nat.lt_irrefl 0)
    · -- base case: `r = 1`
      have hex : (groupCohomology.H1InfRes M S).Exact := groupCohomology.H1InfRes_exact M S
      have h2 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hex
      rw [show (groupCohomology.H1InfRes M S).f = (groupCohomology.infNatTrans k S 1).app M
            from rfl,
        show (groupCohomology.H1InfRes M S).g =
            (groupCohomology.resNatTrans k (G := S) (H := G) S.subtype 1).app M from rfl] at h2
      exact h2
    · -- inductive step: `r = n + 2`
      have h1 : Subsingleton (groupCohomology (Rep.res S.subtype M) 1) :=
        hM 1 (by norm_num) (by omega)
      have hzI : ∀ j, 0 < j → IsZero (groupCohomology (shiftI M) j) := by
        intro j hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
        exact isZero_coind_bot (Rep.res (⊥ : Subgroup G).subtype M) j'
      have hzIS : ∀ j, 0 < j → IsZero (groupCohomology (Rep.res S.subtype (shiftI M)) j) := by
        intro j hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
        exact isZero_groupCohomology_res_coind_bot S (Rep.res (⊥ : Subgroup G).subtype M) j'
      have hzIQ : ∀ j, 0 < j →
          IsZero (groupCohomology ((shiftI M).quotientToInvariants S) j) := by
        intro j hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
        exact isZero_groupCohomology_quotientToInvariants_coind_bot S
          (Rep.res (⊥ : Subgroup G).subtype M) j'
      -- the vanishing hypothesis for the shifted module `C`
      have hC : ∀ j, 0 < j → j < n + 1 →
          Subsingleton (groupCohomology (Rep.res S.subtype (shiftC M)) j) := by
        intro j hj hjlt
        haveI : IsIso ((SS_shortExact M S).δ j (j + 1) rfl) :=
          ShortComplex.ShortExact.isIso_δ (SS_shortExact M S) j (j + 1) rfl (hzIS j hj)
            (hzIS (j + 1) (by omega))
        have hinj : Function.Injective ((SS_shortExact M S).δ j (j + 1) rfl).hom :=
          (ModuleCat.mono_iff_injective _).mp inferInstance
        have hsub : Subsingleton ((SS M S).X₁.homology (j + 1)) :=
          hM (j + 1) (by omega) (by omega)
        haveI := hsub
        exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
      -- the connecting homomorphisms are isomorphisms
      have hα : IsIso ((SG_shortExact M).δ (n + 1) (n + 2) rfl) :=
        ShortComplex.ShortExact.isIso_δ (SG_shortExact M) (n + 1) (n + 2) rfl (hzI (n + 1) (by omega))
          (hzI (n + 2) (by omega))
      have hβ : IsIso ((SS_shortExact M S).δ (n + 1) (n + 2) rfl) :=
        ShortComplex.ShortExact.isIso_δ (SS_shortExact M S) (n + 1) (n + 2) rfl (hzIS (n + 1) (by omega))
          (hzIS (n + 2) (by omega))
      have hγ : IsIso ((SQ_shortExact M S h1).δ (n + 1) (n + 2) rfl) :=
        ShortComplex.ShortExact.isIso_δ (SQ_shortExact M S h1) (n + 1) (n + 2) rfl
          (hzIQ (n + 1) (by omega)) (hzIQ (n + 2) (by omega))
      haveI := hα
      haveI := hβ
      haveI := hγ
      refine range_eq_ker_of_shift
        ((SG_shortExact M).δ (n + 1) (n + 2) rfl).hom
        ((SS_shortExact M S).δ (n + 1) (n + 2) rfl).hom
        ((SQ_shortExact M S h1).δ (n + 1) (n + 2) rfl).hom
        ((groupCohomology.infNatTrans k S (n + 2)).app M).hom
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype (n + 2)).app M).hom
        ((groupCohomology.infNatTrans k S (n + 1)).app (shiftC M)).hom
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype (n + 1)).app
          (shiftC M)).hom
        ?_ ?_ ?_ ?_ ?_ ?_
      · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
      · exact (ModuleCat.mono_iff_injective _).mp inferInstance
      · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
      · show (((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype (n + 2)).app
            M)).hom.comp ((SG_shortExact M).δ (n + 1) (n + 2) rfl).hom
            = ((SS_shortExact M S).δ (n + 1) (n + 2) rfl).hom.comp
              (((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype (n + 1)).app
                (shiftC M))).hom
        exact nat_res M S n
      · show (((groupCohomology.infNatTrans k S (n + 2)).app M)).hom.comp
            ((SQ_shortExact M S h1).δ (n + 1) (n + 2) rfl).hom
            = ((SG_shortExact M).δ (n + 1) (n + 2) rfl).hom.comp
              (((groupCohomology.infNatTrans k S (n + 1)).app (shiftC M))).hom
        exact nat_inf M S n h1
      · exact ih (n + 1) (by omega) (by omega) (shiftC M) hC

end InfResAux


/-- **Inflation–restriction exactness in degree `r` (Milne, Class Field Theory, II.1.34).** Let `S ◁ G` be a normal subgroup, `k` a commutative ring and `A` a `k`-linear `G`-representation. If `H^j(S, A) = 0` for all `0 < j < r`, then the sequence `H^r(G ⧸ S, A^S) → H^r(G, A) → H^r(S, A)` is exact: the range of the inflation map is the kernel of the restriction map (in degrees `r ≥ 1`). This generalises to arbitrary degrees the degree-`2` statement already available in the commons. -/
theorem range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
    {k : Type} [CommRing k] {G : Type} [Group G] (S : Subgroup G) [S.Normal] (A : Rep k G)
    {r : ℕ} (hr : 0 < r)
    (h : ∀ j : ℕ, 0 < j → j < r → Subsingleton (groupCohomology (Rep.res S.subtype A) j)) :
    LinearMap.range ((groupCohomology.infNatTrans k S r).app A).hom =
      LinearMap.ker
        ((groupCohomology.resNatTrans k (G := S) (H := G) S.subtype r).app A).hom :=
  InfResAux.range_infNatTrans_eq_ker_resNatTrans_aux S r hr A h

end

end Commons.RepresentationTheory.GroupCohomology