--Appendix C: Lean 4 Verification
--This appendix supplies a Lean 4 script that verifies the validity of (continued)
-- the core deduction (theorem 4.1), its robustness under revision of the essential (continued)
--property set defining X (corollary 6.1), and a modest conservativity (theorem 6.1) result via (continued)
--a first-order translation. The script uses an uninterpreted time-horizon operator ⊕ and assumes only the modal axiom T.

-- Defining the basic types for the ontology
axiom Kind : Type
axiom Entity : Type
axiom Time : Type
axiom Duration : Type
axiom Laws : Prop --  paper's symbol L

-- Fixing the time operator globally. the operator now takes a Time and a Duration
axiom tPlus : Time → Duration → Time
infixl:65 " ⊕ " => tPlus

-- Declaring the global predicates
axiom essConf : Kind → Entity → Time → Prop
axiom S_rel : Entity → Time → Prop
axiom B : Entity → Time → Prop
axiom Interference_E : Entity → Time → Time → Prop
axiom Necessity : Prop → Prop

-- Stating the axioms of the framework
-- Axiom 3.2 (necessity governs the generalization)
axiom Ax2 : Necessity (∀ (X : Kind) (x' : Entity) (t' : Time),
  ((essConf X x' t' ∧ S_rel x' t' ∧ Laws) → B x' t'))

-- Axiom 3.3 (PES)
axiom Ax3 : ∀ (X : Kind) (x' : Entity) (t' : Time) (Δt' : Duration),
 (essConf X x' t' ∧ ¬ Interference_E x' t' (t' ⊕ Δt'))
  → essConf X x' (t' ⊕ Δt')

-- Modal Axiom T
axiom AxiomT : ∀ φ, Necessity φ → φ

-- Proving Theorem 4.1 (Validity of the Deduction)
theorem theorem_validity
{X : Kind} {x : Entity} {t : Time} {Δt : Duration}
  (p1_instantiation : essConf X x t)
  (p2_stability     : ¬ Interference_E x t (t ⊕ Δt))
  (p3_conditions    : S_rel x (t ⊕ Δt) ∧ Laws)
  : B x (t ⊕ Δt) := by

  -- Step 6: Establishing the future essence
  have future_conf : essConf X x (t ⊕ Δt) := by
    apply Ax3 X x t Δt
    exact And.intro p1_instantiation p2_stability

  -- Step 7: Axiom 3.2 (Stated as Ax2)

  -- Step 8: Applying Axiom T to remove Necessity (BEFORE instantiation)
  have generalization : (∀ (X : Kind) (x' : Entity) (t' : Time),
    ((essConf X x' t' ∧ S_rel x' t' ∧ Laws) → B x' t')) :=
    AxiomT _ Ax2

  -- Step 9: Universal Instantiation
  have material_link :
    ((essConf X x (t ⊕ Δt) ∧ S_rel x (t ⊕ Δt) ∧ Laws) → B x (t ⊕ Δt)) :=
    generalization X x (t ⊕ Δt)

  -- Step 10: Constructing the antecedent
  have antecedent : essConf X x (t ⊕ Δt) ∧ S_rel x (t ⊕ Δt) ∧ Laws := by
    constructor
    · exact future_conf
    · exact p3_conditions

  -- Step 11: Modus Ponens
  exact material_link antecedent

-- Establishing the revised definitions for the Corollary
axiom essConf' : Kind → Entity → Time → Prop

--  Axiom 3.2 (De Dicto)
axiom Ax2' : Necessity (∀ (X : Kind) (x' : Entity) (t' : Time),
  ((essConf' X x' t' ∧ S_rel x' t' ∧ Laws) → B x' t'))

axiom Ax3' : ∀ (X : Kind) (x' : Entity) (t' : Time) (Δt' : Duration),
  (essConf' X x' t' ∧ ¬ Interference_E x' t' (t' ⊕ Δt'))
  → essConf' X x' (t' ⊕ Δt')

-- Proving the Corollary (Revision Robustness)
theorem corollary_revision
{X : Kind} {x : Entity} {t : Time} {Δt : Duration}
  (p1' : essConf' X x t)
  (p2' : ¬ Interference_E x t (t ⊕ Δt))
  (p3' : S_rel x (t ⊕ Δt) ∧ Laws)
  : B x (t ⊕ Δt) := by
  have future_conf' : essConf' X x (t ⊕ Δt) :=
    Ax3' X x t Δt (And.intro p1' p2')

  -- Applying Axiom T first
  have generalization' := AxiomT _ Ax2'

  -- Instantiation
  have material_link' :
      ((essConf' X x (t ⊕ Δt) ∧ S_rel x (t ⊕ Δt) ∧ Laws) → B x (t ⊕ Δt)) :=
    generalization' X x (t ⊕ Δt)

  exact material_link' (And.intro future_conf' p3')

-- Defining the FOL translations for Theorem 6.1
axiom ObsConfig_X    : Entity → Time → Prop
axiom NonInterf_FOL : Entity → Time → Time → Prop
axiom CondLaw_FOL    : Entity → Time → Prop
axiom B_obs          : Entity → Time → Prop

axiom pes_fol :
∀ (x' : Entity) (t' : Time) (Δt' : Duration), (ObsConfig_X x' t' ∧ NonInterf_FOL x' t' (t' ⊕ Δt'))
    → ObsConfig_X x' (t' ⊕ Δt')
axiom link_fol :
  ∀ x' t', (ObsConfig_X x' t' ∧ CondLaw_FOL x' t') → B_obs x' t'

-- Proving Theorem 6.1 (Modest Conservativity)
theorem theorem_conservativity
{x : Entity} {t : Time} {Δt : Duration}
  (p1_fol : ObsConfig_X x t)
  (p2_fol : NonInterf_FOL x t (t ⊕ Δt))
  (p3_fol : CondLaw_FOL x (t ⊕ Δt))
  : B_obs x (t ⊕ Δt) := by
  have future_conf_fol : ObsConfig_X x (t ⊕ Δt) :=
    pes_fol x t Δt (And.intro p1_fol p2_fol)
  exact link_fol x (t ⊕ Δt) (And.intro future_conf_fol p3_fol)
